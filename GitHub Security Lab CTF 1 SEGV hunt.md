# GitHub Security Lab CTF 1: SEGV hunt

[https://securitylab.github.com/ctf/segv/](https://securitylab.github.com/ctf/segv/)

挖GNU C lib（glibc）中的alloca洞，用来给栈分配缓冲区的。不安全的点在于：没有检查是否有足够的栈空间留给缓冲区，如果所需缓冲区太大导致alloca返回一个不可用指针，可能会在读写buffer的时候导致SIGSEGV。所以alloca一般用于分配小buffer。glibc调用了几百次alloca，你要用CodeQL找到没有检查buffer大小的洞

- 找到alloc的宏。它是一个__builtin_alloca扩展的内置函数

```graphql
import cpp
from FunctionCall fc #all calls in program
where fc.getTarget().getName() = "__builtin_alloca"
#getTarget可以获取所有被调用者
select fc
```

- 过滤小buffer

```graphql
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis
import cpp
from Function fc
where fc.getTarget().hasQualifiedName("__builtin_alloca") and (
upperBound(fc.getArgument(0).getFullyConverted()) >= 65536 or
 lowerBound(fc.getArgument(0).getFullyConverted()) < 0
)
#找出特定表达式可以具有的最大和最小范围,发现越界漏洞或整数溢出漏洞时很有用
select fc,fc.getFile().toString() + ":L" + fc.getLocation().getStartLine()
```

- 过滤被`__libc_use_alloca` ********保护的alloc调用

```graphql
import cpp
import semmle.code.cpp.controlflow.Guards
from FunctionCall fc, GuardCondition gc, FunctionCall fc2

string getPostfix(Expr f){
		result = f.getFile().toString() + ":L" +f.getLocation().getStartLine().getStratLine()
}

where fc2.getTarget().hasQualifiedName("__libc_use_alloca")
	and fc.getTarget().hasQualifiedName("__builtin_alloca")
#检测在__alloca进入Basic Block的条件下__libc_use_alloca函数被调用的次数
	and gc.controls(fc.getBasicBlock(), _) #返回 条件语句控制指定基本块 的条件语句
	and gc.getAChild*() = fc2 #保证要找的保护条件是基于__libc_use_alloca
# *是自反传递闭包，应用这个谓词零次或多次（包括它自己）
select gc,getPostfix(gc)
```

- 有时将结果`__libc_use_alloca`赋值给一个变量，然后将其用作保护条件。用`local dataflow`找到此保护条件。

```graphql

import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

string getPostfix(Expr f){
		result = f.getFile().toString() + ":L" +f.getLocation().getStartLine().getStratLine()
}

from FunctionCall fc, FunctionCall fc2, GuardCondition gc,
DataFlow::Node source, DataFlow::Node sink
where fc.getTarget().getName() = "__builtin_alloca"
    and fc2.getTarget().getName() = "__libc_use_alloca"
    and gc.controls(fc.getBasicBlock(), _)
    and DataFlow::localFlow(source , sink)
    and source.asExpr() = fc2 #污染源
    and sink.asExpr() = gc #敏感点
select gc,getPostfix(fc2)
```

- 有时`__libc_use_alloca`会被封装送到到`__builtin_expect`的调用里，过滤闭包找到它

```graphql

import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

string getPostfix(Expr f){
		result = f.getFile().toString() + ":L" +f.getLocation().getStartLine().getStratLine()
}

from FunctionCall fc, FunctionCall fc2, GuardCondition gc,
DataFlow::Node source, DataFlow::Node sink
where fc.getTarget().getName() = "__builtin_alloca"
    and fc2.getTarget().getName() = "__libc_use_alloca"
    and gc.controls(fc.getBasicBlock(), _)
    and DataFlow::localFlow(source , sink)
    and source.asExpr() = fc2
    and sink.asExpr() = gc.getAChild*() 
    # * is Reflexive transitive closure, apply this predicate zero or more times.
    #   gc.getAChild*() means gc and gc's all chlidren
    # __builtin_expect(__libc_use_alloca()), __libc_use_alloca is __builtin_expect's child.
select gc,getPostfix(gc)
```

- 过滤掉！取反的情况，利用[ControlFlowNode](https://codeql.github.com/codeql-standard-libraries/cpp/semmle/code/cpp/controlflow/ControlFlowGraph.qll/type.ControlFlowGraph$ControlFlowNode.html)

```graphql
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

string getPostfix(Expr f){
		result = f.getFile().toString() + ":L" +f.getLocation().getStartLine().getStratLine()
}

from FunctionCall fc, FunctionCall fc2, GuardCondition gc,
GuardCondition guard,BasicBlock block1,BasicBlock block2,
DataFlow::Node source, DataFlow::Node sink

where fc.getTarget().getName() = "__builtin_alloca"
    and fc2.getTarget().getName() = "__libc_use_alloca"
		and block1.contains(fc)
		and guard.controls(block1, _) #包含__builtin_alloca的条件语句
		and DataFlow::localFlow(source,sink)
		and block2.contains(fc2) 
		and source.asExpr() = block2.getANode() #扩大__libc_use_alloca上下游基础块的查找
		and sink.asExpr() = guard.getAChild*()
select guard,getPostfix(guard)
```

- 找到受`__libc_use_alloca`保护的安全的`alloca`调用，加上OOB

```graphql
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

string getPostfix(Expr f){
		result = f.getFile().toString() + ":L" +f.getLocation().getStartLine().getStratLine()
}

predicate isSafeAllocaCall(FunctionCall fc) {
     exists( FunctionCall fc2, GuardCondition gc,
						 DataFlow::Node source, DataFlow::Node sink
			       |   fc2.getTarget().getName() = "__libc_use_alloca"
            and gc.controls(fc.getBasicBlock(), _)
            and DataFlow::localFlow(source , sink)
            and source.asExpr() = fc2.getBasicBlock().getANode()
            and sink.asExpr() = gc.getAChild*() 
        )   
 }

from FunctionCall fc
Where fc.getTarget().hasQualifiedName("__builtin_alloca")
	and isSafeAllocaCall(fc)
	and upperBound(fc.getArgument(0).getFullyConverted()) <65535
	and lowerBound(fc.getArgument(0).getFullyConverted()) > 0
select fc,"is safe calls __alloca()",getPostfix(fc)
```

- 污点跟踪找到不安全的alloca调用，其分配大小被变量所控制且这个变量从file里读取。首先找到fopen。source是fopen的调用，sink是危险调用alloca的参数大小，寻找二者可达路径。

```graphql
import cpp
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.models.interfaces.DataFlow
import semmle.code.cpp.controlflow.Guards
import DataFlow::PathGraph

# Track taint through `__strnlen`.
class StrlenFunction extends DataFlowFunction {
  StrlenFunction() { this.getName().matches("%str%len%") }

  override predicate hasDataFlow(FunctionInput i, FunctionOutput o) {
    i.isParameter(0) and o.isReturnValue()
  }
}

# Track taint through `__getdelim`.
class GetDelimFunction extends DataFlowFunction {
  GetDelimFunction() { this.getName().matches("%get%delim%") }

  override predicate hasDataFlow(FunctionInput i, FunctionOutput o) {
    i.isParameter(3) and o.isParameterDeref(0)
  }
}

class Config extends TaintTracking::Configuration {
  Config() { this = "fopen_to_alloca_taint" }

  override predicate isSource(DataFlow::Node source) {
    exists(FunctionCall fc | 
        fc.getTarget().getName() = "_IO_new_fopen"
        and source.asExpr() = fc
        )
  }

  override predicate isSink(DataFlow::Node sink) {
    exists(Expr sizeExpr, FunctionCall alloca|
        alloca.getTarget().getName() = "__builtin_alloca"
        and not isSafeAllocaCall(alloca)
        and (upperBound(alloca.getArgument(0).getFullyConverted()) >= 65535 or upperBound(alloca.getArgument(0).getFullyConverted()) < 0)
        and sizeExpr = alloca.getArgument(0).getFullyConverted()
        and sink.asExpr() = sizeExpr #sink是危险点
        )
  }
}

from Config cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "fopen flows to alloca"
```

- 分析crashes，调试下输入，利用poc

```graphql
fopen flows to alloca	gconv_conf.c:323:25
Path
1	call to _IO_new_fopen 	gconv_conf.c:369:14
2	rp 	gconv_conf.c:418:14
3	rp 	gconv_conf.c:250:19
4	... + ... 	gconv_conf.c:323:25
```

源头是 read_conf_file 里从 filename 打开的 fp 文件句柄，

解析文件字节流时使用的 (char * )rp 在解析conf文件中的module块时会进入 add_module 并把rp作为实参

```c
/* Read the next configuration file.  */
static void
read_conf_file (const char *filename, const char *directory, size_t dir_len,
		void **modules, size_t *nmodules)
{
  /* Note the file is opened with cancellation in the I/O functions
     disabled.  */
  FILE *fp = fopen (filename, "rce");
  ...
      if (rp - word == sizeof ("alias") - 1
	  && memcmp (word, "alias", sizeof ("alias") - 1) == 0)
	add_alias (rp, *modules);
      else if (rp - word == sizeof ("module") - 1
	       && memcmp (word, "module", sizeof ("module") - 1) == 0)
	add_module (rp, directory, dir_len, modules, nmodules, modcounter++);
      /* else */
	/* Otherwise ignore the line.  */
    }

  free (line);

  fclose (fp);
}
```

在add_module里rp形参被赋给了from

```c
/* Add new module.  */
static void
add_module (char *rp, const char *directory, size_t dir_len, void **modules,
	    size_t *nmodules, int modcounter)
{
  /* We expect now
     1. `from' name
     2. `to' name
     3. filename of the module
     4. an optional cost value
  */
  struct gconv_alias fake_alias;
  struct gconv_module *new_module;
  char *from, *to, *module, *wp;
  int need_ext;
  int cost_hi;

  while (__isspace_l (*rp, _nl_C_locobj_ptr))
    ++rp;
  from = rp;
    ...
    /* See whether we have already an alias with this name defined.  */
  fake_alias.fromname = strndupa (from, to - from);
    ...
}
```

to - from作为strndupa的size实参

而strndupa是使用了alloca实现的strndup，存在_libc_use_alloca保证安全的alloca调用，因此在to-from也就是，即conf 中 module name 极端长的情况下会程序会crash (SIGSEV)

