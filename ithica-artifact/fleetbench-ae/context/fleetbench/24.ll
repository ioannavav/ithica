; ModuleID = '<stdin>'
source_filename = "fpandint.cc"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

module asm ".globl _ZSt21ios_base_library_initv"

@.str = private unnamed_addr constant [40 x i8] c"The result of integer addition is: %d \0A\00", align 1
@0 = private unnamed_addr constant [4 x i8] c"---\00", align 1
@1 = private unnamed_addr constant [18 x i8] c"_Z11addIntegersii\00", align 1
@2 = private unnamed_addr constant [44 x i8] c"Error in function: %s , #Basic block: %d \0A \00", align 1
@3 = private unnamed_addr constant [29 x i8] c"  %_7 = add nsw i32 %_5, %_6\00", align 1
@4 = private unnamed_addr constant [36 x i8] c"Potential Failing Instruction: %s \0A\00", align 1
@5 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@6 = private unnamed_addr constant [56 x i8] c"-------------- Beginning Of Failing Block ------------\0A\00", align 1
@7 = private unnamed_addr constant [44 x i8] c"  %_volatile_alloca1 = alloca i32, align 4\0A\00", align 1
@8 = private unnamed_addr constant [43 x i8] c"  %_volatile_alloca = alloca i32, align 4\0A\00", align 1
@9 = private unnamed_addr constant [29 x i8] c"  %_3 = alloca i32, align 4\0A\00", align 1
@10 = private unnamed_addr constant [29 x i8] c"  %_4 = alloca i32, align 4\0A\00", align 1
@11 = private unnamed_addr constant [36 x i8] c"  store i32 %_0, i32* %_3, align 4\0A\00", align 1
@12 = private unnamed_addr constant [36 x i8] c"  store i32 %_1, i32* %_4, align 4\0A\00", align 1
@13 = private unnamed_addr constant [37 x i8] c"  %_5 = load i32, i32* %_3, align 4\0A\00", align 1
@14 = private unnamed_addr constant [37 x i8] c"  %_6 = load i32, i32* %_4, align 4\0A\00", align 1
@15 = private unnamed_addr constant [30 x i8] c"  %_7 = add nsw i32 %_5, %_6\0A\00", align 1
@16 = private unnamed_addr constant [59 x i8] c"  store volatile i32 %_5, i32* %_volatile_alloca, align 4\0A\00", align 1
@17 = private unnamed_addr constant [60 x i8] c"  %_8 = load volatile i32, i32* %_volatile_alloca, align 4\0A\00", align 1
@18 = private unnamed_addr constant [60 x i8] c"  store volatile i32 %_6, i32* %_volatile_alloca1, align 4\0A\00", align 1
@19 = private unnamed_addr constant [61 x i8] c"  %_9 = load volatile i32, i32* %_volatile_alloca1, align 4\0A\00", align 1
@20 = private unnamed_addr constant [31 x i8] c"  %_10 = add nsw i32 %_8, %_9\0A\00", align 1
@21 = private unnamed_addr constant [41 x i8] c"  %_cmp_result1 = icmp eq i32 %_7, %_10\0A\00", align 1
@22 = private unnamed_addr constant [53 x i8] c"  br i1 %_cmp_result1, label %_then1, label %_else1\0A\00", align 1
@23 = private unnamed_addr constant [58 x i8] c"**************** End Of Failing Block *****************\0A\0A\00", align 1
@24 = private unnamed_addr constant [4 x i8] c"---\00", align 1
@25 = private unnamed_addr constant [21 x i8] c"_Z14multiplyFloatsff\00", align 1
@26 = private unnamed_addr constant [44 x i8] c"Error in function: %s , #Basic block: %d \0A \00", align 1
@27 = private unnamed_addr constant [28 x i8] c"  %_7 = fmul float %_5, %_6\00", align 1
@28 = private unnamed_addr constant [36 x i8] c"Potential Failing Instruction: %s \0A\00", align 1
@29 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@30 = private unnamed_addr constant [56 x i8] c"-------------- Beginning Of Failing Block ------------\0A\00", align 1
@31 = private unnamed_addr constant [46 x i8] c"  %_volatile_alloca1 = alloca float, align 4\0A\00", align 1
@32 = private unnamed_addr constant [45 x i8] c"  %_volatile_alloca = alloca float, align 4\0A\00", align 1
@33 = private unnamed_addr constant [31 x i8] c"  %_3 = alloca float, align 4\0A\00", align 1
@34 = private unnamed_addr constant [31 x i8] c"  %_4 = alloca float, align 4\0A\00", align 1
@35 = private unnamed_addr constant [40 x i8] c"  store float %_0, float* %_3, align 4\0A\00", align 1
@36 = private unnamed_addr constant [40 x i8] c"  store float %_1, float* %_4, align 4\0A\00", align 1
@37 = private unnamed_addr constant [41 x i8] c"  %_5 = load float, float* %_3, align 4\0A\00", align 1
@38 = private unnamed_addr constant [41 x i8] c"  %_6 = load float, float* %_4, align 4\0A\00", align 1
@39 = private unnamed_addr constant [29 x i8] c"  %_7 = fmul float %_5, %_6\0A\00", align 1
@40 = private unnamed_addr constant [63 x i8] c"  store volatile float %_5, float* %_volatile_alloca, align 4\0A\00", align 1
@41 = private unnamed_addr constant [64 x i8] c"  %_8 = load volatile float, float* %_volatile_alloca, align 4\0A\00", align 1
@42 = private unnamed_addr constant [64 x i8] c"  store volatile float %_6, float* %_volatile_alloca1, align 4\0A\00", align 1
@43 = private unnamed_addr constant [65 x i8] c"  %_9 = load volatile float, float* %_volatile_alloca1, align 4\0A\00", align 1
@44 = private unnamed_addr constant [30 x i8] c"  %_10 = fmul float %_8, %_9\0A\00", align 1
@45 = private unnamed_addr constant [44 x i8] c"  %_cmp_result2 = fcmp oeq float %_7, %_10\0A\00", align 1
@46 = private unnamed_addr constant [53 x i8] c"  br i1 %_cmp_result2, label %_then2, label %_else2\0A\00", align 1
@47 = private unnamed_addr constant [58 x i8] c"**************** End Of Failing Block *****************\0A\0A\00", align 1
@48 = private unnamed_addr constant [4 x i8] c"---\00", align 1
@49 = private unnamed_addr constant [5 x i8] c"main\00", align 1
@50 = private unnamed_addr constant [44 x i8] c"Error in function: %s , #Basic block: %d \0A \00", align 1
@51 = private unnamed_addr constant [32 x i8] c"  %_12 = icmp slt i32 %_11, 200\00", align 1
@52 = private unnamed_addr constant [36 x i8] c"Potential Failing Instruction: %s \0A\00", align 1
@53 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@54 = private unnamed_addr constant [56 x i8] c"-------------- Beginning Of Failing Block ------------\0A\00", align 1
@55 = private unnamed_addr constant [38 x i8] c"  %_11 = load i32, i32* %_7, align 4\0A\00", align 1
@56 = private unnamed_addr constant [33 x i8] c"  %_12 = icmp slt i32 %_11, 200\0A\00", align 1
@57 = private unnamed_addr constant [60 x i8] c"  store volatile i32 %_11, i32* %_volatile_alloca, align 4\0A\00", align 1
@58 = private unnamed_addr constant [61 x i8] c"  %_13 = load volatile i32, i32* %_volatile_alloca, align 4\0A\00", align 1
@59 = private unnamed_addr constant [33 x i8] c"  %_14 = icmp slt i32 %_13, 200\0A\00", align 1
@60 = private unnamed_addr constant [41 x i8] c"  %_cmp_result4 = icmp eq i1 %_12, %_14\0A\00", align 1
@61 = private unnamed_addr constant [53 x i8] c"  br i1 %_cmp_result4, label %_then4, label %_else4\0A\00", align 1
@62 = private unnamed_addr constant [58 x i8] c"**************** End Of Failing Block *****************\0A\0A\00", align 1
@63 = private unnamed_addr constant [4 x i8] c"---\00", align 1
@64 = private unnamed_addr constant [5 x i8] c"main\00", align 1
@65 = private unnamed_addr constant [44 x i8] c"Error in function: %s , #Basic block: %d \0A \00", align 1
@66 = private unnamed_addr constant [32 x i8] c"  %_37 = mul nsw i32 %_35, %_36\00", align 1
@67 = private unnamed_addr constant [36 x i8] c"Potential Failing Instruction: %s \0A\00", align 1
@68 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@69 = private unnamed_addr constant [56 x i8] c"-------------- Beginning Of Failing Block ------------\0A\00", align 1
@70 = private unnamed_addr constant [38 x i8] c"  %_33 = load i32, i32* %_2, align 4\0A\00", align 1
@71 = private unnamed_addr constant [38 x i8] c"  %_34 = load i32, i32* %_7, align 4\0A\00", align 1
@72 = private unnamed_addr constant [82 x i8] c"  %_35 = call noundef i32 @_Z11addIntegersii(i32 noundef %_33, i32 noundef %_34)\0A\00", align 1
@73 = private unnamed_addr constant [38 x i8] c"  %_36 = load i32, i32* %_7, align 4\0A\00", align 1
@74 = private unnamed_addr constant [33 x i8] c"  %_37 = mul nsw i32 %_35, %_36\0A\00", align 1
@75 = private unnamed_addr constant [61 x i8] c"  store volatile i32 %_35, i32* %_volatile_alloca2, align 4\0A\00", align 1
@76 = private unnamed_addr constant [62 x i8] c"  %_38 = load volatile i32, i32* %_volatile_alloca2, align 4\0A\00", align 1
@77 = private unnamed_addr constant [61 x i8] c"  store volatile i32 %_36, i32* %_volatile_alloca3, align 4\0A\00", align 1
@78 = private unnamed_addr constant [62 x i8] c"  %_39 = load volatile i32, i32* %_volatile_alloca3, align 4\0A\00", align 1
@79 = private unnamed_addr constant [33 x i8] c"  %_40 = mul nsw i32 %_38, %_39\0A\00", align 1
@80 = private unnamed_addr constant [37 x i8] c"  store i32 %_37, i32* %_8, align 4\0A\00", align 1
@81 = private unnamed_addr constant [42 x i8] c"  %_41 = load float, float* %_4, align 4\0A\00", align 1
@82 = private unnamed_addr constant [42 x i8] c"  %_42 = load float, float* %_5, align 4\0A\00", align 1
@83 = private unnamed_addr constant [91 x i8] c"  %_43 = call noundef float @_Z14multiplyFloatsff(float noundef %_41, float noundef %_42)\0A\00", align 1
@84 = private unnamed_addr constant [41 x i8] c"  store float %_43, float* %_9, align 4\0A\00", align 1
@85 = private unnamed_addr constant [38 x i8] c"  %_44 = load i32, i32* %_8, align 4\0A\00", align 1
@86 = private unnamed_addr constant [136 x i8] c"  %_45 = call i32 (i8*, ...) @printf(i8* noundef getelementptr inbounds ([40 x i8], [40 x i8]* @.str, i64 0, i64 0), i32 noundef %_44)\0A\00", align 1
@87 = private unnamed_addr constant [42 x i8] c"  %_cmp_result5 = icmp eq i32 %_37, %_40\0A\00", align 1
@88 = private unnamed_addr constant [53 x i8] c"  br i1 %_cmp_result5, label %_then5, label %_else5\0A\00", align 1
@89 = private unnamed_addr constant [58 x i8] c"**************** End Of Failing Block *****************\0A\0A\00", align 1
@90 = private unnamed_addr constant [4 x i8] c"---\00", align 1
@91 = private unnamed_addr constant [5 x i8] c"main\00", align 1
@92 = private unnamed_addr constant [44 x i8] c"Error in function: %s , #Basic block: %d \0A \00", align 1
@93 = private unnamed_addr constant [29 x i8] c"  %_77 = add nsw i32 %_76, 1\00", align 1
@94 = private unnamed_addr constant [36 x i8] c"Potential Failing Instruction: %s \0A\00", align 1
@95 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@96 = private unnamed_addr constant [56 x i8] c"-------------- Beginning Of Failing Block ------------\0A\00", align 1
@97 = private unnamed_addr constant [38 x i8] c"  %_76 = load i32, i32* %_7, align 4\0A\00", align 1
@98 = private unnamed_addr constant [30 x i8] c"  %_77 = add nsw i32 %_76, 1\0A\00", align 1
@99 = private unnamed_addr constant [61 x i8] c"  store volatile i32 %_76, i32* %_volatile_alloca8, align 4\0A\00", align 1
@100 = private unnamed_addr constant [62 x i8] c"  %_78 = load volatile i32, i32* %_volatile_alloca8, align 4\0A\00", align 1
@101 = private unnamed_addr constant [30 x i8] c"  %_79 = add nsw i32 %_78, 1\0A\00", align 1
@102 = private unnamed_addr constant [37 x i8] c"  store i32 %_77, i32* %_7, align 4\0A\00", align 1
@103 = private unnamed_addr constant [42 x i8] c"  %_cmp_result6 = icmp eq i32 %_77, %_79\0A\00", align 1
@104 = private unnamed_addr constant [53 x i8] c"  br i1 %_cmp_result6, label %_then6, label %_else6\0A\00", align 1
@105 = private unnamed_addr constant [58 x i8] c"**************** End Of Failing Block *****************\0A\0A\00", align 1

; Function Attrs: mustprogress noinline nounwind optnone uwtable
define dso_local noundef i32 @_Z11addIntegersii(i32 noundef %0, i32 noundef %1) #0 {
  %volatile_alloca1 = alloca i32, align 4
  %volatile_alloca = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  store i32 %1, i32* %4, align 4
  %5 = load i32, i32* %3, align 4
  %6 = load i32, i32* %4, align 4
  %7 = add nsw i32 %5, %6
  store volatile i32 %5, i32* %volatile_alloca, align 4
  %8 = load volatile i32, i32* %volatile_alloca, align 4
  store volatile i32 %6, i32* %volatile_alloca1, align 4
  %9 = load volatile i32, i32* %volatile_alloca1, align 4
  %10 = add nsw i32 %8, %9
  %cmp_result1 = icmp eq i32 %7, %10
  br i1 %cmp_result1, label %then1, label %else1

else1:                                            ; preds = %2
  call void @print_cpu_id()
  call void @print_date(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @0, i32 0, i32 0))
  %11 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @2, i32 0, i32 0), i8* getelementptr inbounds ([18 x i8], [18 x i8]* @1, i32 0, i32 0), i32 1)
  %alloca1 = alloca [64 x i8], align 1
  %alloca2 = alloca [64 x i8], align 1
  %12 = bitcast [64 x i8]* %alloca1 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %12, i8 0, i32 64, i1 true)
  %13 = bitcast [64 x i8]* %alloca2 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %13, i8 0, i32 64, i1 true)
  %14 = bitcast [64 x i8]* %alloca1 to i32*
  %15 = bitcast [64 x i8]* %alloca2 to i32*
  store volatile i32 %7, i32* %14, align 4
  store volatile i32 %10, i32* %15, align 4
  %pointerCast = bitcast i32* %14 to i8*
  %pointerCast2 = bitcast i32* %15 to i8*
  %16 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @4, i32 0, i32 0), i8* getelementptr inbounds ([29 x i8], [29 x i8]* @3, i32 0, i32 0))
  %17 = call i32* @printMemoryAsHex(i8* %pointerCast, i32 64, i8* %pointerCast2, i32 64)
  %18 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @5, i32 0, i32 0))
  %19 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([56 x i8], [56 x i8]* @6, i32 0, i32 0))
  %20 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @7, i32 0, i32 0))
  %21 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([43 x i8], [43 x i8]* @8, i32 0, i32 0))
  %22 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @9, i32 0, i32 0))
  %23 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @10, i32 0, i32 0))
  %24 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @11, i32 0, i32 0))
  %25 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @12, i32 0, i32 0))
  %26 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @13, i32 0, i32 0))
  %27 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @14, i32 0, i32 0))
  %28 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @15, i32 0, i32 0))
  %29 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([59 x i8], [59 x i8]* @16, i32 0, i32 0))
  %30 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([60 x i8], [60 x i8]* @17, i32 0, i32 0))
  %31 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([60 x i8], [60 x i8]* @18, i32 0, i32 0))
  %32 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([61 x i8], [61 x i8]* @19, i32 0, i32 0))
  %33 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @20, i32 0, i32 0))
  %34 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @21, i32 0, i32 0))
  %35 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @22, i32 0, i32 0))
  %36 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([58 x i8], [58 x i8]* @23, i32 0, i32 0))
  br label %then1

then1:                                            ; preds = %else1, %2
  ret i32 %7
}

; Function Attrs: mustprogress noinline nounwind optnone uwtable
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
  br i1 %cmp_result2, label %then2, label %else2

else2:                                            ; preds = %2
  call void @print_cpu_id()
  call void @print_date(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @24, i32 0, i32 0))
  %11 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @26, i32 0, i32 0), i8* getelementptr inbounds ([21 x i8], [21 x i8]* @25, i32 0, i32 0), i32 2)
  %alloca1 = alloca [64 x i8], align 1
  %alloca2 = alloca [64 x i8], align 1
  %12 = bitcast [64 x i8]* %alloca1 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %12, i8 0, i32 64, i1 true)
  %13 = bitcast [64 x i8]* %alloca2 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %13, i8 0, i32 64, i1 true)
  %14 = bitcast [64 x i8]* %alloca1 to float*
  %15 = bitcast [64 x i8]* %alloca2 to float*
  store volatile float %7, float* %14, align 4
  store volatile float %10, float* %15, align 4
  %pointerCast = bitcast float* %14 to i8*
  %pointerCast2 = bitcast float* %15 to i8*
  %16 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @28, i32 0, i32 0), i8* getelementptr inbounds ([28 x i8], [28 x i8]* @27, i32 0, i32 0))
  %17 = call i32* @printMemoryAsHex(i8* %pointerCast, i32 64, i8* %pointerCast2, i32 64)
  %18 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @29, i32 0, i32 0))
  %19 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([56 x i8], [56 x i8]* @30, i32 0, i32 0))
  %20 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([46 x i8], [46 x i8]* @31, i32 0, i32 0))
  %21 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([45 x i8], [45 x i8]* @32, i32 0, i32 0))
  %22 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @33, i32 0, i32 0))
  %23 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([31 x i8], [31 x i8]* @34, i32 0, i32 0))
  %24 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @35, i32 0, i32 0))
  %25 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([40 x i8], [40 x i8]* @36, i32 0, i32 0))
  %26 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @37, i32 0, i32 0))
  %27 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @38, i32 0, i32 0))
  %28 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @39, i32 0, i32 0))
  %29 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([63 x i8], [63 x i8]* @40, i32 0, i32 0))
  %30 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([64 x i8], [64 x i8]* @41, i32 0, i32 0))
  %31 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([64 x i8], [64 x i8]* @42, i32 0, i32 0))
  %32 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([65 x i8], [65 x i8]* @43, i32 0, i32 0))
  %33 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @44, i32 0, i32 0))
  %34 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @45, i32 0, i32 0))
  %35 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @46, i32 0, i32 0))
  %36 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([58 x i8], [58 x i8]* @47, i32 0, i32 0))
  br label %then2

then2:                                            ; preds = %else2, %2
  ret float %7
}

; Function Attrs: mustprogress noinline norecurse optnone uwtable
define dso_local noundef i32 @main() #1 {
  %volatile_alloca8 = alloca i32, align 4
  %volatile_alloca3 = alloca i32, align 4
  %volatile_alloca2 = alloca i32, align 4
  %volatile_alloca = alloca i32, align 4
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca float, align 4
  %5 = alloca float, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca float, align 4
  store i32 0, i32* %1, align 4
  store i32 5, i32* %2, align 4
  store i32 3, i32* %3, align 4
  store float 4.500000e+00, float* %4, align 4
  store float 0x4002666660000000, float* %5, align 4
  store i32 1, i32* %6, align 4
  store i32 0, i32* %7, align 4
  br label %10

10:                                               ; preds = %then6, %0
  %11 = load i32, i32* %7, align 4
  %12 = icmp slt i32 %11, 200
  store volatile i32 %11, i32* %volatile_alloca, align 4
  %13 = load volatile i32, i32* %volatile_alloca, align 4
  %14 = icmp slt i32 %13, 200
  %cmp_result4 = icmp eq i1 %12, %14
  br i1 %cmp_result4, label %then4, label %else4

else4:                                            ; preds = %10
  call void @print_cpu_id()
  call void @print_date(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @48, i32 0, i32 0))
  %15 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @50, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @49, i32 0, i32 0), i32 4)
  %alloca1 = alloca [64 x i8], align 1
  %alloca2 = alloca [64 x i8], align 1
  %16 = bitcast [64 x i8]* %alloca1 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %16, i8 0, i32 64, i1 true)
  %17 = bitcast [64 x i8]* %alloca2 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %17, i8 0, i32 64, i1 true)
  %18 = bitcast [64 x i8]* %alloca1 to i1*
  %19 = bitcast [64 x i8]* %alloca2 to i1*
  store volatile i1 %12, i1* %18, align 1
  store volatile i1 %14, i1* %19, align 1
  %pointerCast = bitcast i1* %18 to i8*
  %pointerCast1 = bitcast i1* %19 to i8*
  %20 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @52, i32 0, i32 0), i8* getelementptr inbounds ([32 x i8], [32 x i8]* @51, i32 0, i32 0))
  %21 = call i32* @printMemoryAsHex(i8* %pointerCast, i32 64, i8* %pointerCast1, i32 64)
  %22 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @53, i32 0, i32 0))
  %23 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([56 x i8], [56 x i8]* @54, i32 0, i32 0))
  %24 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @55, i32 0, i32 0))
  %25 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @56, i32 0, i32 0))
  %26 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([60 x i8], [60 x i8]* @57, i32 0, i32 0))
  %27 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([61 x i8], [61 x i8]* @58, i32 0, i32 0))
  %28 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @59, i32 0, i32 0))
  %29 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @60, i32 0, i32 0))
  %30 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @61, i32 0, i32 0))
  %31 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([58 x i8], [58 x i8]* @62, i32 0, i32 0))
  br label %then4

then4:                                            ; preds = %else4, %10
  br i1 %12, label %32, label %98

32:                                               ; preds = %then4
  %33 = load i32, i32* %2, align 4
  %34 = load i32, i32* %7, align 4
  %35 = call noundef i32 @_Z11addIntegersii(i32 noundef %33, i32 noundef %34)
  %36 = load i32, i32* %7, align 4
  %37 = mul nsw i32 %35, %36
  store volatile i32 %35, i32* %volatile_alloca2, align 4
  %38 = load volatile i32, i32* %volatile_alloca2, align 4
  store volatile i32 %36, i32* %volatile_alloca3, align 4
  %39 = load volatile i32, i32* %volatile_alloca3, align 4
  %40 = mul nsw i32 %38, %39
  store i32 %37, i32* %8, align 4
  %41 = load float, float* %4, align 4
  %42 = load float, float* %5, align 4
  %43 = call noundef float @_Z14multiplyFloatsff(float noundef %41, float noundef %42)
  store float %43, float* %9, align 4
  %44 = load i32, i32* %8, align 4
  %45 = call i32 (i8*, ...) @printf(i8* noundef getelementptr inbounds ([40 x i8], [40 x i8]* @.str, i64 0, i64 0), i32 noundef %44)
  %cmp_result5 = icmp eq i32 %37, %40
  br i1 %cmp_result5, label %then5, label %else5

else5:                                            ; preds = %32
  call void @print_cpu_id()
  call void @print_date(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @63, i32 0, i32 0))
  %46 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @65, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @64, i32 0, i32 0), i32 5)
  %alloca14 = alloca [64 x i8], align 1
  %alloca25 = alloca [64 x i8], align 1
  %47 = bitcast [64 x i8]* %alloca14 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %47, i8 0, i32 64, i1 true)
  %48 = bitcast [64 x i8]* %alloca25 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %48, i8 0, i32 64, i1 true)
  %49 = bitcast [64 x i8]* %alloca14 to i32*
  %50 = bitcast [64 x i8]* %alloca25 to i32*
  store volatile i32 %37, i32* %49, align 4
  store volatile i32 %40, i32* %50, align 4
  %pointerCast6 = bitcast i32* %49 to i8*
  %pointerCast7 = bitcast i32* %50 to i8*
  %51 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @67, i32 0, i32 0), i8* getelementptr inbounds ([32 x i8], [32 x i8]* @66, i32 0, i32 0))
  %52 = call i32* @printMemoryAsHex(i8* %pointerCast6, i32 64, i8* %pointerCast7, i32 64)
  %53 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @68, i32 0, i32 0))
  %54 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([56 x i8], [56 x i8]* @69, i32 0, i32 0))
  %55 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @70, i32 0, i32 0))
  %56 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @71, i32 0, i32 0))
  %57 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([82 x i8], [82 x i8]* @72, i32 0, i32 0))
  %58 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @73, i32 0, i32 0))
  %59 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @74, i32 0, i32 0))
  %60 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([61 x i8], [61 x i8]* @75, i32 0, i32 0))
  %61 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([62 x i8], [62 x i8]* @76, i32 0, i32 0))
  %62 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([61 x i8], [61 x i8]* @77, i32 0, i32 0))
  %63 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([62 x i8], [62 x i8]* @78, i32 0, i32 0))
  %64 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([33 x i8], [33 x i8]* @79, i32 0, i32 0))
  %65 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @80, i32 0, i32 0))
  %66 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @81, i32 0, i32 0))
  %67 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @82, i32 0, i32 0))
  %68 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([91 x i8], [91 x i8]* @83, i32 0, i32 0))
  %69 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([41 x i8], [41 x i8]* @84, i32 0, i32 0))
  %70 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @85, i32 0, i32 0))
  %71 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([136 x i8], [136 x i8]* @86, i32 0, i32 0))
  %72 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @87, i32 0, i32 0))
  %73 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @88, i32 0, i32 0))
  %74 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([58 x i8], [58 x i8]* @89, i32 0, i32 0))
  br label %then5

then5:                                            ; preds = %else5, %32
  br label %75

75:                                               ; preds = %then5
  %76 = load i32, i32* %7, align 4
  %77 = add nsw i32 %76, 1
  store volatile i32 %76, i32* %volatile_alloca8, align 4
  %78 = load volatile i32, i32* %volatile_alloca8, align 4
  %79 = add nsw i32 %78, 1
  store i32 %77, i32* %7, align 4
  %cmp_result6 = icmp eq i32 %77, %79
  br i1 %cmp_result6, label %then6, label %else6

else6:                                            ; preds = %75
  call void @print_cpu_id()
  call void @print_date(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @90, i32 0, i32 0))
  %80 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @92, i32 0, i32 0), i8* getelementptr inbounds ([5 x i8], [5 x i8]* @91, i32 0, i32 0), i32 6)
  %alloca19 = alloca [64 x i8], align 1
  %alloca210 = alloca [64 x i8], align 1
  %81 = bitcast [64 x i8]* %alloca19 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %81, i8 0, i32 64, i1 true)
  %82 = bitcast [64 x i8]* %alloca210 to i8*
  call void @llvm.memset.p0i8.i32(i8* align 8 %82, i8 0, i32 64, i1 true)
  %83 = bitcast [64 x i8]* %alloca19 to i32*
  %84 = bitcast [64 x i8]* %alloca210 to i32*
  store volatile i32 %77, i32* %83, align 4
  store volatile i32 %79, i32* %84, align 4
  %pointerCast11 = bitcast i32* %83 to i8*
  %pointerCast12 = bitcast i32* %84 to i8*
  %85 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([36 x i8], [36 x i8]* @94, i32 0, i32 0), i8* getelementptr inbounds ([29 x i8], [29 x i8]* @93, i32 0, i32 0))
  %86 = call i32* @printMemoryAsHex(i8* %pointerCast11, i32 64, i8* %pointerCast12, i32 64)
  %87 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @95, i32 0, i32 0))
  %88 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([56 x i8], [56 x i8]* @96, i32 0, i32 0))
  %89 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @97, i32 0, i32 0))
  %90 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @98, i32 0, i32 0))
  %91 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([61 x i8], [61 x i8]* @99, i32 0, i32 0))
  %92 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([62 x i8], [62 x i8]* @100, i32 0, i32 0))
  %93 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @101, i32 0, i32 0))
  %94 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @102, i32 0, i32 0))
  %95 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @103, i32 0, i32 0))
  %96 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @104, i32 0, i32 0))
  %97 = call i32 (...) @fprintFunc(i8* getelementptr inbounds ([58 x i8], [58 x i8]* @105, i32 0, i32 0))
  br label %then6

then6:                                            ; preds = %else6, %75
  br label %10, !llvm.loop !6

98:                                               ; preds = %then4
  ret i32 0
}

declare i32 @printf(i8* noundef, ...) #2

declare i32 @fprintFunc(...)

declare void @print_cpu_id()

declare void @print_date(i8*)

; Function Attrs: argmemonly nofree nounwind willreturn writeonly
declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i1 immarg) #3

declare i32* @printMemoryAsHex(i8*, i32, i8*, i32)

attributes #0 = { mustprogress noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress noinline norecurse optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { argmemonly nofree nounwind willreturn writeonly }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Debian clang version 14.0.6"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
