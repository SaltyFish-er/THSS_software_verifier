/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/
using System;
using System.IO;
using System.Collections.Generic;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class BasicPath{
        public List<Block> blockList;
        public Expression postCondition;
        public Expression predCondition;
        public List<Expression> postRankingFunction;
        public BasicPath(List<Block> blocks,Expression post,Expression pred){
            Expression t = new BoolConstantExpression(true);
            this.blockList = blocks;
            this.postCondition = post;
            this.predCondition = pred;
            this.postRankingFunction = new List<Expression>();
        }
    }
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public Expression wlp_AssertStatement(AssertStatement st,Expression post){
            post = new AndExpression(st.pred,post);
            return post;
        }
        public Expression wlp_VariableAssignStatement(VariableAssignStatement st,Expression post){
            post = post.Substitute(st.variable,st.rhs);
            return post;
        }
        public Expression wlp_SubscriptAssignStatement(SubscriptAssignStatement st,Expression post){
            VariableExpression array = new VariableExpression(st.array);
            VariableExpression arrayLength = new VariableExpression(st.array.length);
            ArrayUpdateExpression expr = new ArrayUpdateExpression(array,st.subscript,st.rhs,arrayLength);
            post = post.Substitute(st.array,expr);
            return post;
        }
        public Expression wlp_AssumeStatement(AssumeStatement st,Expression post){
            post = new ImplicationExpression(st.condition,post);
            return post;
        }

        public Expression wlp_FunctionCallStatement(FunctionCallStatement st,Expression post){
            Expression predCondition = new BoolConstantExpression(true);
            Expression postCondition = new BoolConstantExpression(true);
            Function func = st.rhs.function;
            
            //调用前满足前置条件：  assert \phi
            PreconditionBlock predBlock = func.preconditionBlock;
            for(int i = 0;i<predBlock.conditions.Count;i++){
                Expression newPredCondition = predBlock.conditions[i];
                for(int j = 0;j<func.parameters.Count;j++){
                    VariableExpression variableExpr = new VariableExpression(st.rhs.argumentVariables[j]);
                    newPredCondition = newPredCondition.Substitute(func.parameters[j],variableExpr);
                }
                predCondition = new AndExpression(predCondition,newPredCondition);
            }
            //调用后返回值满足后置条件： assume \psi
            PostconditionBlock postBlock = func.postconditionBlock;
            for(int i = 0;i<postBlock.conditions.Count;i++){
                Expression newPostCondition = postBlock.conditions[i];
                for(int j = 0;j<st.lhs.Count;j++){
                    VariableExpression variableExpr = new VariableExpression(st.lhs[j]);
                    newPostCondition = newPostCondition.Substitute(func.rvs[j],variableExpr);
                }
                for(int j = 0;j<func.parameters.Count;j++){
                    VariableExpression variableExpr = new VariableExpression(st.rhs.argumentVariables[j]);
                    newPostCondition = newPostCondition.Substitute(func.parameters[j],variableExpr);
                }
                postCondition = new AndExpression(postCondition,newPostCondition);
            }
            //组合起来
            Expression vc = new ImplicationExpression(postCondition,post);
            vc = new AndExpression(vc,predCondition);
            return vc;
        }
        public Expression wlp(Statement st,Expression post){
            if (st is AssertStatement ast1){
                post = wlp_AssertStatement(ast1,post);
            }
            else if (st is AssignStatement){
                if(st is VariableAssignStatement ast2){
                    post =  wlp_VariableAssignStatement(ast2,post);
                }
                else if(st is SubscriptAssignStatement ast3){
                    post = wlp_SubscriptAssignStatement(ast3,post);
                }
            }
            else if (st is AssumeStatement ast4){
                post = wlp_AssumeStatement(ast4,post);
            }
            else if (st is FunctionCallStatement ast5){
                post = wlp_FunctionCallStatement(ast5,post);
            }
            return post;
        }

        public Expression visitPostCondBlock(PostconditionBlock postBlock){
            Expression vc = new BoolConstantExpression(true);

            foreach (Expression post in postBlock.conditions){
                vc = new AndExpression(vc,post);
            }

            return vc;
        }
        //访问过程块：包括LoopBlock BasicBlock
        //访问LoopBlock时仅处理statement不处理invariants和ranking Functions
        //返回最弱前置条件
        public Expression visitProcessBlock(Block block,Expression post){

            if(block.statements.Last != null){
                LinkedListNode<Statement> st =  block.statements.Last;
                bool flag = true;
                while(flag){
                    flag = false;
                    post = wlp(st.Value,post);
                    if(st.Previous != null){
                        st = st.Previous;
                        flag = true;
                    }
                }
            }
            return post;
        }
        //访问循环头块，获得invariants
        public Expression visitLoopBlock(LoopHeadBlock loopblock){
            Expression invariant = new BoolConstantExpression(true);
            foreach(Expression expr in loopblock.invariants){
                invariant = new AndExpression(invariant,expr);
            }
            return invariant;
        }
        public Expression visitPreCondBlock(PreconditionBlock predBlock){
            Expression pred = new BoolConstantExpression(true);
            
            //visit requirement conditions
            foreach (Expression condition in predBlock.conditions){
                pred = new AndExpression(pred,condition);
            }
            return pred;
        }
        public Expression visitBasicPath(BasicPath path){
            Expression post = path.postCondition;
            for(int i = path.blockList.Count-1;i>=0;i--){
                post = visitProcessBlock(path.blockList[i],post);
            }
            Expression vc = new ImplicationExpression(path.predCondition,post);
            if(path.blockList[0] is HeadBlock predBlock){
                if(predBlock.rankingFunctions.Count>0){
                    if(predBlock is LoopHeadBlock){
                        Expression predBlockCondition = visitLoopBlock((LoopHeadBlock) predBlock);
                        Expression rankingFunctionCondition = new GEExpression(predBlock.rankingFunctions[0],new IntConstantExpression(0));
                        Expression positiveCondition = new ImplicationExpression(predBlockCondition,rankingFunctionCondition);
                        vc = new AndExpression(vc,positiveCondition);
                    }
                    if(predBlock is PreconditionBlock){
                        Expression predBlockCondition = visitPreCondBlock((PreconditionBlock) predBlock);
                        Expression rankingFunctionCondition = new GEExpression(predBlock.rankingFunctions[0],new IntConstantExpression(0));
                        Expression positiveCondition = new ImplicationExpression(predBlockCondition,rankingFunctionCondition);
                        vc = new AndExpression(vc,positiveCondition);
                    }                   
                }
                if(path.postRankingFunction.Count>0 && predBlock.rankingFunctions.Count>0){
                    Expression predRankingFunction = predBlock.rankingFunctions[0];
                    List<LocalVariable> oldVariableList = new List<LocalVariable>(path.postRankingFunction[0].GetFreeVariables());
                    List<LocalVariable> newVariableList = new List<LocalVariable>();
                    Expression postRankingFunction = path.postRankingFunction[0];
                    foreach(LocalVariable oldVariable in oldVariableList){
                        LocalVariable newVariable = new LocalVariable();
                        newVariable.name = oldVariable.name + "___";
                        newVariable.type = oldVariable.type;
                        newVariableList.Add(newVariable);
                        VariableExpression newVariableExpr = new VariableExpression(newVariable);
                        postRankingFunction = postRankingFunction.Substitute(oldVariable,newVariableExpr);
                    }
                    Expression postCondition = new LTExpression(predRankingFunction,postRankingFunction);  
                    for(int i = path.blockList.Count-1;i>=0;i--){
                        postCondition = visitProcessBlock(path.blockList[i],postCondition);
                    }
                    Expression vc1 = new ImplicationExpression(path.predCondition,postCondition);
                    for(int i = 0; i < newVariableList.Count;i++){
                        VariableExpression oldVariableExpr = new VariableExpression(oldVariableList[i]);
                        vc1 = vc1.Substitute(newVariableList[i],oldVariableExpr);
                    }
                    vc = new AndExpression(vc,vc1);
                }
            }
            //Console.WriteLine("verification: ");
            //vc.Print(writer);
            //Console.WriteLine("\n");
            return vc;
        }
        // 从某一个结点向下寻找到 PostBlock 或 LoopBlock 的路径
        // startBlock:当前开始搜索的结点
        // BasicPathList：（一个过程中）总的基本路径集合
        // Path2Block：从某个出发点到当前块(startBlock)的路径，不包括当前块
        // record：当前已经访问过的块
        public void getPath(Block startBlock,List<BasicPath> BasicPathList,
                            List<Block> Path2Block,List<Block> record){
            //判断是否求过该结点的路径
            for(int i = 0; i < record.Count;i++){
                if (Equals(startBlock,record[i])){
                    return;
                }
            }
            Path2Block.Add(startBlock);
            record.Add(startBlock);
            //通过startBlock的每个后继去查找路径
            if(startBlock.successors.First!=null){
                LinkedListNode<Block> child = startBlock.successors.First;
                bool flag = true; //记录child.Next是否为null
                while(flag){
                    flag = false;
                    List<Block> tempPath2Block = new List<Block>(Path2Block.ToArray());
                    if(child.Value is PostconditionBlock postBlock){
                        if(tempPath2Block[0] is PreconditionBlock predBlock){
                            Expression pred = visitPreCondBlock(predBlock);
                            Expression post = visitPostCondBlock(postBlock);
                            BasicPath newPath = new BasicPath(tempPath2Block,post,pred);
                            BasicPathList.Add(newPath);
                        }
                        else if(tempPath2Block[0] is LoopHeadBlock loopBlock){
                            Expression pred = visitLoopBlock(loopBlock);
                            Expression post = visitPostCondBlock(postBlock);
                            BasicPath newPath = new BasicPath(tempPath2Block,post,pred);
                            BasicPathList.Add(newPath);
                        }
                    }
                    else if(child.Value is LoopHeadBlock loopTailBlock){
                        if(tempPath2Block[0] is PreconditionBlock predBlock){
                            Expression pred = visitPreCondBlock(predBlock);
                            Expression post = visitLoopBlock(loopTailBlock);
                            BasicPath newPath = new BasicPath(tempPath2Block,post,pred);
                            BasicPathList.Add(newPath);
                        }
                        else if(tempPath2Block[0] is LoopHeadBlock loopBlock){
                            Expression pred = visitLoopBlock(loopBlock);
                            Expression post = visitLoopBlock(loopTailBlock);
                            BasicPath newPath = new BasicPath(tempPath2Block,post,pred);
                            for(int i = 0 ;i<loopTailBlock.rankingFunctions.Count;i++){
                                newPath.postRankingFunction.Add(loopTailBlock.rankingFunctions[i]);
                            }
                            BasicPathList.Add(newPath);
                        }
                        List<Block> newPath2Blcok = new List<Block>();
                        getPath(child.Value,BasicPathList,newPath2Blcok,record);
                    }
                    else{
                        getPath(child.Value,BasicPathList,tempPath2Block,record);
                    }
                    //迭代至startBlock的下一个后继
                    if (child.Next != null){
                        child = child.Next;
                        flag = true;
                    }
                }
            }
        }

        public Expression visitFunction(Function function){
            Expression vc = new BoolConstantExpression(true);
            //获取基本路径
            List<BasicPath> pathList = new List<BasicPath>();
            List<Block> path2Block = new List<Block>();
            List<Block> record = new List<Block>();
            getPath(function.preconditionBlock,pathList,path2Block,record);
            //逐个分析基本路径
            foreach(BasicPath path in pathList){
                Expression vc1 = visitBasicPath(path); 
                vc = new AndExpression(vc,vc1);
            }
            return vc;
        }
        public int Apply(IRMain cfg)
        {
            Expression vc = new BoolConstantExpression(true);

            if(cfg.predicates.First!=null){
                LinkedListNode<Predicate> predicate = cfg.predicates.First;
                bool flag = true;
                while (flag){
                    flag = false;
                    solver.definePredicate(predicate.Value);
                    if(predicate.Next!=null){
                        flag = true;
                        predicate = predicate.Next;
                    }
                }
            }

            if(cfg.functions.First!=null){
                LinkedListNode<Function> function = cfg.functions.First;
                bool flag = true;
                while(flag){
                    flag = false;
                    vc = new AndExpression(visitFunction(function.Value),vc);
                    if(function.Next!=null){
                        flag = true;
                        function = function.Next;
                    }
                }
            }
            if(solver.CheckValid(vc) == null){
                return 1;
            }
            else{
                return -1;
            }
        }
    }
}