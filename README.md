# Use of ITHICA passes 

We explain how to use the ITHICA compiler passes and provide examples of how different ITHICA passes transform an example input program. 
For each ITHICA transformation, we present the original LLVM IR code and the transformed code after applying a pass. 
The transformations include:

- **ArithmeticPass.cpp**: Implements the Arith transformation of ITHICA paper. It duplicates arithmetic instructions and checks their results using Functional Consistency (FC) checks. 
- **MemPass.cpp**: Implements the Mem transformation of ITHICA paper. Instruments memory instructions (loads and stores). It duplicates loads, while for stores it inserts loads from the same memory. It checks their results using Functional Consistency (FC) checks for loads and Round Trip Consistency (RTC) checks for stores. 
- **MemDivPass.cpp**: Implements the MemDiv transformation of ITHICA paper. Similar to MemPass.cpp, but introduces memory fences and cache line flushes to check different levels of the memory hierarchy. 
- **BranchPass.cpp**: Implements the Br transformation of ITHICA paper. Checks that conditional branches are resolved successfully between the two valid destinations using Control Flow Integrity (CFI) checks. 

## How to use:
Build `.so` from `.cpp`:
```
 clang++ -shared -o [PassName].so -DBLOCKSIZE=X -DINTERLEAVING=Y -DLIBRARYNAME="Z" -fPIC [PassName].cpp `llvm-config --cxxflags`
```

Pass the `.so` on the original `.ll`:
```
opt -load ./[PassName].so --enable-new-pm=0 -[passname] -S < [original].ll > [transformed].ll
```
Example:
```
clang++ -shared -o [PassName].so -DBLOCKSIZE=1 -DINTERLEAVING=1 -DLIBRARYNAME=\"top level code\" -fPIC [PassName].cpp `llvm-config --cxxflags`
opt -load ./ArithmeticPass.so --enable-new-pm=0 -arithmeticpass -S < fpandint.ll > modified_fpandint.ll
```
At runtime, the modified executable needs to be linked against `libpassmmap`, which contains helper C functions. Compile it with:
```
clang mmap_file.c -fPIC -Wno-format-security -c -o libpassmmap

```

To produce the `.ll` file from the `.cpp` file, and from that the modified executable:
```
clang++ [-O2] -emit-llvm -S fpandint.cc -o fpandint.ll
clang++ [-static] fpandint.ll ./libpassmmap -o modified_fpandint
```

Alternatively, to use the pass directly on a C/C++ file and create the transformed executable, without producing its LLVM IR as an intermediate step:
```
clang++ [-O2] [-static] -c -flegacy-pass-manager -Xclang -load -Xclang ./[PassName].so fpandint.cc -o modified_fpandint
```


#### Parameter selection:
- Block size (X): Choose from `1`, `2`, `4`, `8` or `0` (0 = "dep". Inserts checks right before the instruction dependency chain gets broken)
- Interleaving (Y): Choose from `1`, `2`, `4`, `8` or `0` (0 = "max". Places the duplicate instructions right before the end of the basic block)
- Library name (Z): Specify your program's/library's name. This string is printed upon detecting an error. If instrumenting both top-level code and libraries, you can use this to identify the part of the code where the error occurred.

#### Dependencies:
Version of clang used: 14.0.6

## 1) Example use of Arith transformation
### Original .ll code:
```llvm
define dso_local noundef i32 @_Z11addIntegersii(i32 noundef %0, i32 noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %5 = load i32, i32* %3, align 4
  %6 = load i32, i32* %4, align 4
  %7 = add nsw i32 %5, %6
  ret i32 %7
}
```

### After applying ArithmeticPass.cpp:
```llvm
define dso_local noundef float @_Z14multiplyFloatsff(float noundef %0, float noundef %1) #0 {
  %volatile_alloca1 = alloca float, align 4
  %volatile_alloca = alloca float, align 4
  %3 = alloca float, align 4
  %4 = alloca float, align 4
  store float %0, float* %3, align 4
  store float %1, float* %4, align 4
  %5 = load float, float* %3, align 4
  %6 = load float, float* %4, align 4
  %7 = fmul float %5, %6
  store volatile float %5, float* %volatile_alloca, align 4
  %8 = load volatile float, float* %volatile_alloca, align 4
  store volatile float %6, float* %volatile_alloca1, align 4
  %9 = load volatile float, float* %volatile_alloca1, align 4
  %10 = fmul float %8, %9
  %cmp_result2 = fcmp oeq float %7, %10
  br i1 %cmp_result2, label %then, label %else

else:                                            
  call void @print_cpu_id()
  [...]
  br label %then

then:                                            
  ret float %7
}
```
## 2) Example use of Mem transformation
### After applying MemPass.cpp:
```llvm
define dso_local noundef i32 @_Z11addIntegersii(i32 noundef %0, i32 noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  %5 = load volatile i32, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %6 = load volatile i32, i32* %4, align 4
  %7 = load i32, i32* %3, align 4
  %8 = load volatile i32, i32* %3, align 4
  %9 = load i32, i32* %4, align 4
  %10 = load volatile i32, i32* %4, align 4
  %11 = add nsw i32 %7, %9
  %cmp_result1 = icmp eq i32 %0, %5
  %cmp_result11 = icmp eq i32 %1, %6
  %cmp_result12 = icmp eq i32 %7, %8
  %cmp_result13 = icmp eq i32 %9, %10
  %init_agg_cmp = and i1 %cmp_result1, %cmp_result11
  %agg_cmp = and i1 %init_agg_cmp, %cmp_result12
  %agg_cmp4 = and i1 %agg_cmp, %cmp_result13
  br i1 %agg_cmp4, label %then, label %else

else:                                            
  call void @print_cpu_id()
  [...]
  br label %then

then:                                            
  ret i32 %11
}
```

## 3) Example use of MemDiv transformation
### After applying MemDivPass.cpp:
```llvm
define dso_local noundef i32 @_Z11addIntegersii(i32 noundef %0, i32 noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  %5 = load volatile i32, i32* %3, align 4
  call void asm sideeffect "mfence", ""()
  %6 = load volatile i32, i32* %3, align 4
  call void asm sideeffect "clflush $0", "m"(i32* %3)
  %7 = load volatile i32, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %8 = load volatile i32, i32* %4, align 4
  call void asm sideeffect "mfence", ""()
  %9 = load volatile i32, i32* %4, align 4
  call void asm sideeffect "clflush $0", "m"(i32* %4)
  %10 = load volatile i32, i32* %4, align 4
  %11 = load i32, i32* %3, align 4
  call void asm sideeffect "clflush $0", "m"(i32* %3)
  %12 = load volatile i32, i32* %3, align 4
  %13 = load i32, i32* %4, align 4
  call void asm sideeffect "clflush $0", "m"(i32* %4)
  %14 = load volatile i32, i32* %4, align 4
  %15 = add nsw i32 %11, %13
  %cmp_result1 = icmp eq i32 %0, %5
  %cmp_result11 = icmp eq i32 %0, %6
  %cmp_result12 = icmp eq i32 %0, %7
  %cmp_result13 = icmp eq i32 %1, %8
  %cmp_result14 = icmp eq i32 %1, %9
  %cmp_result15 = icmp eq i32 %1, %10
  %cmp_result16 = icmp eq i32 %11, %12
  %cmp_result17 = icmp eq i32 %13, %14
  %init_agg_cmp = and i1 %cmp_result1, %cmp_result11
  %agg_cmp = and i1 %init_agg_cmp, %cmp_result12
  %agg_cmp8 = and i1 %agg_cmp, %cmp_result13
  %agg_cmp9 = and i1 %agg_cmp8, %cmp_result14
  %agg_cmp10 = and i1 %agg_cmp9, %cmp_result15
  %agg_cmp11 = and i1 %agg_cmp10, %cmp_result16
  %agg_cmp12 = and i1 %agg_cmp11, %cmp_result17
  br i1 %agg_cmp12, label %then, label %else

else:                                            
  call void @print_cpu_id()
  [...]
  br label %then

then:                                            
  ret i32 %11
}
```

## 4) Example use of Br transformation
### Original .ll code:
```llvm
define i32 @main(i32 %argc, i8** %argv) {
entry:
    %cmp = icmp sgt i32 %argc, 1         ; Check if argc (argument count) is greater than 1
    br i1 %cmp, label %if_true, label %if_false

if_true:                                 ; If condition is true
    %true_msg = getelementptr [19 x i8], [19 x i8]* @.str_true, i32 0, i32 0
    call i32 (i8*, ...) @printf(i8* %true_msg)
    br label %end

if_false:                                ; If condition is false
    %false_msg = getelementptr [20 x i8], [20 x i8]* @.str_false, i32 0, i32 0
    call i32 (i8*, ...) @printf(i8* %false_msg)
    br label %end

end:                                     ; End block
    ret i32 0
}
```

### After applying BranchPass.cpp:
```llvm
define i32 @main(i32 %argc, i8** %argv) {
entry:
  %cmp = icmp sgt i32 %argc, 0
  %0 = select i1 %cmp, i32 2, i32 3
  store i32 %0, i32* @llvmPassBranchTargetAddress, align 4
  store i1 true, i1* @llvmPassBranchCheckingON, align 1
  br i1 %cmp, label %if_true, label %if_false

if_true:                                          ; preds = %entry
  %1 = load i1, i1* @llvmPassBranchCheckingON, align 1
  br i1 %1, label %checkBB, label %skipCheckBB

origBB:                                           ; preds = %skipCheckBB, %thenBB
  %true_msg = getelementptr [19 x i8], [19 x i8]* @.str_true, i32 0, i32 0
  %2 = call i32 (i8*, ...) @printf(i8* %true_msg)
  br label %end

if_false:                                         ; preds = %entry
  %3 = load i1, i1 0, align 1
  br i1 %3, label %checkBB2, label %skipCheckBB3

origBB1:                                          ; preds = %skipCheckBB3, %thenBB4
  %false_msg = getelementptr [20 x i8], [20 x i8]* @.str_false, i32 0, i32 0
  %4 = call i32 (i8*, ...) @printf(i8* %false_msg)
  br label %end

end:                                              ; preds = %origBB1, %origBB
  ret i32 0

checkBB:                                          ; preds = %if_true
  %5 = load i32, i32* @llvmPassBranchTargetAddress, align 4
  %6 = icmp eq i32 %5, 2
  br i1 %6, label %thenBB, label %errorBB

skipCheckBB:                                      ; preds = %if_true
  br label %origBB

thenBB:                                           ; preds = %checkBB
  store i1 false, i1* @llvmPassBranchCheckingON, align 1
  br label %origBB

errorBB:
[...]
```
