; ModuleID = 'Test.pas'
source_filename = "Test.pas"
target datalayout = "e-m:w-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-gnu"

%NativeInt = type i64
%SizeInt = type i64
%LongDouble = type double

%Test.TTestRec = type [4 x i8]
@Test.I = global i32 zeroinitializer
@Test.Z = global [5 x i32] zeroinitializer
@Test.Ptr = global %Test.TTestRec* zeroinitializer
@Test.$with1 = global %Test.TTestRec* zeroinitializer
declare noalias i8* @malloc(i64) nounwind
declare void @free(i8* nocapture) nounwind
@System.Shortint.$typeinfo = external global i8*
@System.Byte.$typeinfo = external global i8*
@System.Smallint.$typeinfo = external global i8*
@System.Word.$typeinfo = external global i8*
@System.Longint.$typeinfo = external global i8*
@System.LongWord.$typeinfo = external global i8*
@System.Int64.$typeinfo = external global i8*
@System.UInt64.$typeinfo = external global i8*
@System.Integer.$typeinfo = external global i8*
@System.Cardinal.$typeinfo = external global i8*
@System.String.$typeinfo = external global i8*
@System.AnsiString.$typeinfo = external global i8*
@System.WideString.$typeinfo = external global i8*
@System.UnicodeString.$typeinfo = external global i8*

define internal fastcc %Test.TTestRec* @Test.MakeRecord(i32 %IL)
{
	%Result.addr = alloca %Test.TTestRec*, align 8

	%IL.addr = alloca i32, align 4
	store i32 %IL, i32* %IL.addr

	%.1 = bitcast i8* null to %Test.TTestRec*
	store %Test.TTestRec* %.1, %Test.TTestRec** %Result.addr
	%.2 = bitcast %Test.TTestRec** %Result.addr to i8**
	%.3 = sext i8 4 to i64
	%.4 = tail call noalias i8* @malloc(i64 %.3) nounwind
	store i8* %.4, i8** %.2
	%.5 = load %Test.TTestRec*, %Test.TTestRec** %Result.addr
	%.6 = getelementptr %Test.TTestRec, %Test.TTestRec* %.5, %SizeInt 0, %SizeInt 0
	%.7 = bitcast i8* %.6 to i32*
	%.8 = load i32, i32* %IL.addr
	store i32 %.8, i32* %.7
	br label %.quit
.quit:
	%.9 = load %Test.TTestRec*, %Test.TTestRec** %Result.addr
	ret %Test.TTestRec* %.9
}

define internal fastcc i32 @Test.Test(i32* %P, i32 %Count)
{
	%Result.addr = alloca i32, align 4

	%P.addr = alloca i32*, align 8
	store i32* %P, i32** %P.addr

	%Count.addr = alloca i32, align 4
	store i32 %Count, i32* %Count.addr

	%I.addr = alloca i32, align 4

	%J.addr = alloca i32, align 4

	%.V1.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	%.2 = sext i8 0 to i32
	store i32 %.2, i32* %I.addr
	%.3 = load i32, i32* %Count.addr
	%.4 = sub i32 %.3, 1
	store i32 %.4, i32* %.V1.addr
	br label %for1.begin
for1.begin:
	%.5 = load i32, i32* %I.addr
	%.6 = load i32, i32* %.V1.addr
	%.7 = icmp sle i32 %.5, %.6
	br i1 %.7, label %forloop1, label %for1.br
forloop1:
	%.8 = load i32, i32* %I.addr
	%.9 = sext i32 %.8 to i64
	%.10 = load i32*, i32** %P.addr
	%.11 = getelementptr i32, i32* %.10, %SizeInt %.9
	%.12 = load i32, i32* %Result.addr
	%.13 = load i32, i32* %.11
	%.14 = add i32 %.12, %.13
	store i32 %.14, i32* %Result.addr
	br label %for1.cont
for1.cont:
	%.15 = load i32, i32* %I.addr
	%.16 = add i32 %.15, 1
	store i32 %.16, i32* %I.addr
	br label %for1.begin
for1.br:
	%.17 = sext i8 2 to i32
	store i32 %.17, i32* %J.addr
	%.18 = load i32, i32* %J.addr
	%.19 = load i32, i32* %Result.addr
	%.20 = add i32 %.19, %.18
	store i32 %.20, i32* %Result.addr
	br label %.quit
.quit:
	%.21 = load i32, i32* %Result.addr
	ret i32 %.21
}

define fastcc void @Test.$main()
{
	%.V1.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* @Test.I
	%.2 = sext i8 4 to i32
	store i32 %.2, i32* %.V1.addr
	br label %for1.begin
for1.begin:
	%.3 = load i32, i32* @Test.I
	%.4 = load i32, i32* %.V1.addr
	%.5 = icmp sle i32 %.3, %.4
	br i1 %.5, label %forloop1, label %for1.br
forloop1:
	%.6 = load i32, i32* @Test.I
	%.7 = sext i32 %.6 to i64
	%.8 = getelementptr [5 x i32], [5 x i32]* @Test.Z, %SizeInt 0, %SizeInt %.7
	%.9 = load i32, i32* @Test.I
	store i32 %.9, i32* %.8
	br label %for1.cont
for1.cont:
	%.10 = load i32, i32* @Test.I
	%.11 = add i32 %.10, 1
	store i32 %.11, i32* @Test.I
	br label %for1.begin
for1.br:
	%.12 = sext i8 0 to i64
	%.13 = getelementptr [5 x i32], [5 x i32]* @Test.Z, %SizeInt 0, %SizeInt %.12
	%.14 = bitcast i32* %.13 to i8*
	%.15 = bitcast i8* %.14 to i32*
	%.16 = sext i8 5 to i32
	%.17 = call fastcc i32 @Test.Test(i32* %.15, i32 %.16)
	%.18 = call fastcc %Test.TTestRec* @Test.MakeRecord(i32 %.17)
	store %Test.TTestRec* %.18, %Test.TTestRec** @Test.Ptr
	%.19 = load %Test.TTestRec*, %Test.TTestRec** @Test.Ptr
	store %Test.TTestRec* %.19, %Test.TTestRec** @Test.$with1
	%.20 = load %Test.TTestRec*, %Test.TTestRec** @Test.$with1
	%.21 = getelementptr %Test.TTestRec, %Test.TTestRec* %.20, %SizeInt 0, %SizeInt 0
	%.22 = bitcast i8* %.21 to i32*
	%.23 = sext i8 1 to i32
	store i32 %.23, i32* %.22
	%.24 = load %Test.TTestRec*, %Test.TTestRec** @Test.$with1
	%.25 = getelementptr %Test.TTestRec, %Test.TTestRec* %.24, %SizeInt 0, %SizeInt 0
	%.26 = bitcast i8* %.25 to i32*
	%.27 = sext i8 2 to i32
	store i32 %.27, i32* %.26
	%.28 = load %Test.TTestRec*, %Test.TTestRec** @Test.$with1
	%.29 = getelementptr %Test.TTestRec, %Test.TTestRec* %.28, %SizeInt 0, %SizeInt 0
	%.30 = bitcast i8* %.29 to i32*
	%.31 = sext i8 3 to i32
	store i32 %.31, i32* %.30
	%.32 = load %Test.TTestRec*, %Test.TTestRec** @Test.$with1
	%.33 = getelementptr %Test.TTestRec, %Test.TTestRec* %.32, %SizeInt 0, %SizeInt 0
	%.34 = bitcast i8* %.33 to i32*
	%.35 = sext i8 4 to i32
	store i32 %.35, i32* %.34
	%.36 = load %Test.TTestRec*, %Test.TTestRec** @Test.$with1
	%.37 = getelementptr %Test.TTestRec, %Test.TTestRec* %.36, %SizeInt 0, %SizeInt 0
	%.38 = bitcast i8* %.37 to i32*
	%.39 = sext i8 5 to i32
	store i32 %.39, i32* %.38
	%.40 = load %Test.TTestRec*, %Test.TTestRec** @Test.Ptr
	%.41 = bitcast %Test.TTestRec* %.40 to i8*
	tail call void @free(i8* %.41) nounwind
	br label %.quit
.quit:
	ret void
}

define i32 @main(i32 %argc, i8** %argv)
{
	call fastcc void @Test.$main()
	ret i32 0
}
