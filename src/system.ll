; ModuleID = 'System.pas'
source_filename = "System.pas"
target datalayout = "e-m:w-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-gnu"

%NativeInt = type i64
%SizeInt = type i64
%LongDouble = type double

@System.Shortint.$typeinfo.data = unnamed_addr constant <{i8, i8, [8 x i8], i8, i32, i32}> <{i8 1, i8 8, [8 x i8] c"Shortint", i8 0, i32 127, i32 128}>
@System.Shortint.$typeinfo = global i8* bitcast(<{i8, i8, [8 x i8], i8, i32, i32}>* @System.Shortint.$typeinfo.data to i8*)
@System.Byte.$typeinfo.data = unnamed_addr constant <{i8, i8, [4 x i8], i8, i32, i32}> <{i8 1, i8 4, [4 x i8] c"Byte", i8 1, i32 255, i32 0}>
@System.Byte.$typeinfo = global i8* bitcast(<{i8, i8, [4 x i8], i8, i32, i32}>* @System.Byte.$typeinfo.data to i8*)
@System.Smallint.$typeinfo.data = unnamed_addr constant <{i8, i8, [8 x i8], i8, i32, i32}> <{i8 1, i8 8, [8 x i8] c"Smallint", i8 2, i32 32767, i32 32768}>
@System.Smallint.$typeinfo = global i8* bitcast(<{i8, i8, [8 x i8], i8, i32, i32}>* @System.Smallint.$typeinfo.data to i8*)
@System.Word.$typeinfo.data = unnamed_addr constant <{i8, i8, [4 x i8], i8, i32, i32}> <{i8 1, i8 4, [4 x i8] c"Word", i8 3, i32 65535, i32 0}>
@System.Word.$typeinfo = global i8* bitcast(<{i8, i8, [4 x i8], i8, i32, i32}>* @System.Word.$typeinfo.data to i8*)
@System.Longint.$typeinfo.data = unnamed_addr constant <{i8, i8, [7 x i8], i8, i32, i32}> <{i8 1, i8 7, [7 x i8] c"Longint", i8 4, i32 2147483647, i32 -2147483648}>
@System.Longint.$typeinfo = global i8* bitcast(<{i8, i8, [7 x i8], i8, i32, i32}>* @System.Longint.$typeinfo.data to i8*)
@System.LongWord.$typeinfo.data = unnamed_addr constant <{i8, i8, [8 x i8], i8, i32, i32}> <{i8 1, i8 8, [8 x i8] c"LongWord", i8 5, i32 -1, i32 0}>
@System.LongWord.$typeinfo = global i8* bitcast(<{i8, i8, [8 x i8], i8, i32, i32}>* @System.LongWord.$typeinfo.data to i8*)
@System.Integer.$typeinfo.data = unnamed_addr constant <{i8, i8, [7 x i8], i8, i32, i32}> <{i8 1, i8 7, [7 x i8] c"Integer", i8 4, i32 2147483647, i32 -2147483648}>
@System.Integer.$typeinfo = global i8* bitcast(<{i8, i8, [7 x i8], i8, i32, i32}>* @System.Integer.$typeinfo.data to i8*)
@System.Cardinal.$typeinfo.data = unnamed_addr constant <{i8, i8, [8 x i8], i8, i32, i32}> <{i8 1, i8 8, [8 x i8] c"Cardinal", i8 5, i32 -1, i32 0}>
@System.Cardinal.$typeinfo = global i8* bitcast(<{i8, i8, [8 x i8], i8, i32, i32}>* @System.Cardinal.$typeinfo.data to i8*)
@System.Int64.$typeinfo.data = unnamed_addr constant <{i8, i8, [5 x i8], i8, i64, i64}> <{i8 16, i8 5, [5 x i8] c"Int64", i8 4, i64 9223372036854775807, i64 -9223372036854775808}>
@System.Int64.$typeinfo = global i8* bitcast(<{i8, i8, [5 x i8], i8, i64, i64}>* @System.Int64.$typeinfo.data to i8*)
@System.UInt64.$typeinfo.data = unnamed_addr constant <{i8, i8, [6 x i8], i8, i64, i64}> <{i8 16, i8 6, [6 x i8] c"UInt64", i8 5, i64 -1, i64 0}>
@System.UInt64.$typeinfo = global i8* bitcast(<{i8, i8, [6 x i8], i8, i64, i64}>* @System.UInt64.$typeinfo.data to i8*)
@System.String.$typeinfo.data = unnamed_addr constant <{i8, i8, [6 x i8]}> <{i8 10, i8 6, [6 x i8] c"String"}>
@System.String.$typeinfo = global i8* bitcast(<{i8, i8, [6 x i8]}>* @System.String.$typeinfo.data to i8*)
@System.AnsiString.$typeinfo.data = unnamed_addr constant <{i8, i8, [10 x i8]}> <{i8 10, i8 10, [10 x i8] c"AnsiString"}>
@System.AnsiString.$typeinfo = global i8* bitcast(<{i8, i8, [10 x i8]}>* @System.AnsiString.$typeinfo.data to i8*)
@System.WideString.$typeinfo.data = unnamed_addr constant <{i8, i8, [10 x i8]}> <{i8 11, i8 10, [10 x i8] c"WideString"}>
@System.WideString.$typeinfo = global i8* bitcast(<{i8, i8, [10 x i8]}>* @System.WideString.$typeinfo.data to i8*)
@System.UnicodeString.$typeinfo.data = unnamed_addr constant <{i8, i8, [13 x i8]}> <{i8 18, i8 13, [13 x i8] c"UnicodeString"}>
@System.UnicodeString.$typeinfo = global i8* bitcast(<{i8, i8, [13 x i8]}>* @System.UnicodeString.$typeinfo.data to i8*)
@System.Variant.$typeinfo.data = unnamed_addr constant <{i8, i8, [7 x i8]}> <{i8 12, i8 7, [7 x i8] c"Variant"}>
@System.Variant.$typeinfo = global i8* bitcast(<{i8, i8, [7 x i8]}>* @System.Variant.$typeinfo.data to i8*)
@System.OleVariant.$typeinfo.data = unnamed_addr constant <{i8, i8, [10 x i8]}> <{i8 12, i8 10, [10 x i8] c"OleVariant"}>
@System.OleVariant.$typeinfo = global i8* bitcast(<{i8, i8, [10 x i8]}>* @System.OleVariant.$typeinfo.data to i8*)
@System._EmptySet = private  unnamed_addr constant [32 x i8] zeroinitializer
@System.TObject.$name =  unnamed_addr constant {%SizeInt, %SizeInt, [8 x i8]} {%SizeInt -1, %SizeInt 7, [8 x i8] c"TObject\00"}
%System.TObject.$vmt.t = type [19 x i8*]
@System.TObject.$vmt = global %System.TObject.$vmt.t [
  i8* bitcast(i8** getelementptr(%System.TObject.$vmt.t, %System.TObject.$vmt.t* @System.TObject.$vmt, %SizeInt 0, %SizeInt 19) to i8*)
  ,i8* null
  ,i8* null
  ,i8* null
  ,i8* null
  ,i8* null
  ,i8* null
  ,i8* null
  ,i8* getelementptr({%SizeInt, %SizeInt, [8 x i8]}, {%SizeInt, %SizeInt, [8 x i8]}* @System.TObject.$name, %SizeInt 0, i32 2, %SizeInt 0)
  ,i8* inttoptr(%SizeInt 8 to i8*)
  ,i8* null
;--- vmt start
  ,i8* bitcast(i32 (i8*, i8*, i8*)* @System.TObject.SafeCallException to i8*)
  ,i8* bitcast(void (i8*)* @System.TObject.AfterConstruction to i8*)
  ,i8* bitcast(void (i8*)* @System.TObject.BeforeDestruction to i8*)
  ,i8* bitcast(void (i8*, i8*)* @System.TObject.Dispatch to i8*)
  ,i8* bitcast(void (i8*, i8*)* @System.TObject.DefaultHandler to i8*)
  ,i8* bitcast(i8* (i8*)* @System.TObject.NewInstance to i8*)
  ,i8* bitcast(void (i8*)* @System.TObject.FreeInstance to i8*)
  ,i8* bitcast(void (i8*, i8)* @System.TObject.Destroy to i8*)
]
%System.TInterfaceTable = type [320008 x i8]
%System.TInterfaceEntry = type [32 x i8]
@System.TObject.InitInstance.$with1 = global %System.TInterfaceEntry* zeroinitializer
%System.MethRec = type [16 x i8]
%System.TGUID = type [16 x i8]
%System.TDispatchMessage = type [2 x i8]
%System.TMethod = type [16 x i8]
%System.TUCS4CharArray = type [251658240 x i32]
%System.IntegerArray = type [251658240 x i32]
%System.PointerArray = type [536870911 x i8*]
%System.TPCharArray = type [268435455 x i8*]
%System.TVarArrayBound = type [8 x i8]
%System.TVarArrayBoundArray = type [1 x %System.TVarArrayBound]
%System.TVarArrayCoorArray = type [1 x i32]
%System.TVarArray = type [32 x i8]
%System.TVarData = type [16 x i8]
%System.TVarRec = type [8 x i8]
%System.AnsiStrRec = type [16 x i8]
@System.ErrorProc = private global void (i8, i8*)* zeroinitializer
@System._EmptyStr = global i8 0
@System._EmptyWStr = global i16 0
%System.GetDynaMethod.TDynaMethodTable = type [20000002 x i8]
declare noalias i8* @malloc(i64) nounwind
declare void @free(i8* nocapture) nounwind

define fastcc i8* @System.TObject.Create(i8* %.vmt, i8 %.flag)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%$exptr.addr = alloca i8*, align 8

	%$exsel.addr = alloca i32, align 4

	br label %.quit
.quit:
	%.1 = load i8*, i8** %Result.addr
	ret i8* %.1
}

define fastcc void @System.TObject.Free(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%.1 = icmp ne i8* %Self, null
	br i1 %.1, label %if1.true, label %if1.false
if1.true:
	%.2 = bitcast i8* %Self to i8***
	%.3 = load i8**, i8*** %.2
	%.4 = getelementptr i8*, i8** %.3, %SizeInt -1
	%.5 = load i8*, i8** %.4
	%.6 = bitcast i8* %.5 to void (i8*, i8)*
	;; IsTypePrefix=false,IsClassrefPrefix=false,IsCtorInner=false,IsDtorInner=false
	call fastcc void %.6(i8* %Self, i8 1)
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System.TObject.InitInstance(i8* %Self, i8* %Instance)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%Instance.addr = alloca i8*, align 8
	store i8* %Instance, i8** %Instance.addr

	%IntfTable.addr = alloca %System.TInterfaceTable*, align 8

	%ClassPtr.addr = alloca i8*, align 8

	%I.addr = alloca i32, align 4

	%.V1.addr = alloca i32, align 4

	%.1 = load i8*, i8** %Instance.addr
	%.2 = bitcast i8* %.1 to i8*
	%.3 = call fastcc i64 @System.TObject.InstanceSize(i8* %Self)
	call fastcc void @System.FillChar(i8* %.2, i64 %.3, i8 0)
	%.4 = bitcast i8** %Instance.addr to i64**
	%.5 = load i64*, i64** %.4
	%.6 = ptrtoint i8* %Self to i64
	store i64 %.6, i64* %.5
	store i8* %Self, i8** %ClassPtr.addr
	br label %while1.begin
while1.begin:
	%.7 = load i8*, i8** %ClassPtr.addr
	%.8 = icmp ne i8* %.7, null
	br i1 %.8, label %while1.body, label %while1.end
while1.body:
	%.9 = load i8*, i8** %ClassPtr.addr
	%.10 = call fastcc %System.TInterfaceTable* @System.TObject.GetInterfaceTable(i8* %.9)
	store %System.TInterfaceTable* %.10, %System.TInterfaceTable** %IntfTable.addr
	%.11 = load %System.TInterfaceTable*, %System.TInterfaceTable** %IntfTable.addr
	%.12 = bitcast i8* null to %System.TInterfaceTable*
	%.13 = icmp ne %System.TInterfaceTable* %.11, %.12
	br i1 %.13, label %if2.true, label %if2.false
if2.true:
	%.14 = sext i8 0 to i32
	store i32 %.14, i32* %I.addr
	%.15 = load %System.TInterfaceTable*, %System.TInterfaceTable** %IntfTable.addr
	%.16 = getelementptr %System.TInterfaceTable, %System.TInterfaceTable* %.15, %SizeInt 0, %SizeInt 0
	%.17 = bitcast i8* %.16 to i32*
	%.18 = load i32, i32* %.17
	%.19 = sext i8 1 to i32
	%.20 = sub i32 %.18, %.19
	store i32 %.20, i32* %.V1.addr
	br label %for3.begin
for3.begin:
	%.21 = load i32, i32* %I.addr
	%.22 = load i32, i32* %.V1.addr
	%.23 = icmp sle i32 %.21, %.22
	br i1 %.23, label %forloop1, label %for3.br
forloop1:
	%.24 = load i32, i32* %I.addr
	%.25 = sext i32 %.24 to i64
	%.26 = load %System.TInterfaceTable*, %System.TInterfaceTable** %IntfTable.addr
	%.27 = getelementptr %System.TInterfaceTable, %System.TInterfaceTable* %.26, %SizeInt 0, %SizeInt 4
	%.28 = bitcast i8* %.27 to [10000 x %System.TInterfaceEntry]*
	%.29 = getelementptr [10000 x %System.TInterfaceEntry], [10000 x %System.TInterfaceEntry]* %.28, %SizeInt 0, %SizeInt %.25
	store %System.TInterfaceEntry* %.29, %System.TInterfaceEntry** @System.TObject.InitInstance.$with1
	%.30 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** @System.TObject.InitInstance.$with1
	%.31 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.30, %SizeInt 0, %SizeInt 16
	%.32 = bitcast i8* %.31 to i8**
	%.33 = load i8*, i8** %.32
	%.34 = icmp ne i8* %.33, null
	br i1 %.34, label %if4.true, label %if4.false
if4.true:
	%.35 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** @System.TObject.InitInstance.$with1
	%.36 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.35, %SizeInt 0, %SizeInt 24
	%.37 = bitcast i8* %.36 to i32*
	%.38 = load i32, i32* %.37
	%.39 = sext i32 %.38 to i64
	%.40 = load i8*, i8** %Instance.addr
	%.41 = getelementptr i8, i8* %.40, %SizeInt %.39
	%.42 = bitcast i8* %.41 to i64*
	%.43 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** @System.TObject.InitInstance.$with1
	%.44 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.43, %SizeInt 0, %SizeInt 16
	%.45 = bitcast i8* %.44 to i8**
	%.46 = bitcast i8** %.45 to i64*
	%.47 = load i64, i64* %.46
	store i64 %.47, i64* %.42
	br label %if4.false
if4.false:
	br label %for3.cont
for3.cont:
	%.48 = load i32, i32* %I.addr
	%.49 = add i32 %.48, 1
	store i32 %.49, i32* %I.addr
	br label %for3.begin
for3.br:
	br label %if2.false
if2.false:
	%.50 = load i8*, i8** %ClassPtr.addr
	%.51 = call fastcc i8* @System.TObject.ClassParent(i8* %.50)
	store i8* %.51, i8** %ClassPtr.addr
	br label %while1.end
while1.end:
	%.52 = load i8*, i8** %Instance.addr
	store i8* %.52, i8** %Result.addr
	br label %.quit
.quit:
	%.53 = load i8*, i8** %Result.addr
	ret i8* %.53
}

define fastcc void @System.TObject.CleanupInstance(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%ClassPtr.addr = alloca i8*, align 8

	%InitTable.addr = alloca i8*, align 8

	%.1 = call fastcc i8* @System.TObject.ClassType(i8* %Self)
	store i8* %.1, i8** %ClassPtr.addr
	%.2 = bitcast i8** %ClassPtr.addr to i64*
	%.3 = load i64, i64* %.2
	%.4 = zext i32 -64 to i64
	%.5 = add i64 %.3, %.4
	%.6 = inttoptr i64 %.5 to i8**
	%.7 = load i8*, i8** %.6
	store i8* %.7, i8** %InitTable.addr
	br label %while1.begin
while1.begin:
	br label %expr1.1
expr1.1:
	%.8 = load i8*, i8** %ClassPtr.addr
	%.9 = icmp ne i8* %.8, null
	br i1 %.9, label %expr1.2, label %expr1.3
expr1.2:
	%.10 = load i8*, i8** %InitTable.addr
	%.11 = icmp ne i8* %.10, null
	br label %expr1.3
expr1.3:
	%.12 = phi i1 [ %.9, %expr1.1], [ %.11, %expr1.2 ]
	br i1 %.12, label %while1.body, label %while1.end
while1.body:
	%.13 = load i8*, i8** %InitTable.addr
	%.14 = call fastcc i8* @System._FinalizeRecord(i8* %Self, i8* %.13)
	%.15 = load i8*, i8** %ClassPtr.addr
	%.16 = call fastcc i8* @System.TObject.ClassParent(i8* %.15)
	store i8* %.16, i8** %ClassPtr.addr
	%.17 = load i8*, i8** %ClassPtr.addr
	%.18 = icmp ne i8* %.17, null
	br i1 %.18, label %if2.true, label %if2.false
if2.true:
	%.19 = bitcast i8** %ClassPtr.addr to i64*
	%.20 = load i64, i64* %.19
	%.21 = zext i32 -64 to i64
	%.22 = add i64 %.20, %.21
	%.23 = inttoptr i64 %.22 to i8**
	%.24 = load i8*, i8** %.23
	store i8* %.24, i8** %InitTable.addr
	br label %if2.false
if2.false:
	br label %while1.end
while1.end:
	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System.TObject.ClassType(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%.1 = bitcast i8* %Self to i8**
	%.2 = load i8*, i8** %.1
	store i8* %.2, i8** %Result.addr
	br label %.quit
.quit:
	%.3 = load i8*, i8** %Result.addr
	ret i8* %.3
}

define fastcc void @System.TObject.ClassName(i8* %Self, [257 x i8]* %Result.addr)
{
	%Self.addr = alloca i8*, align 8

	%.1 = getelementptr i8, i8* %Self, i32 -44
	%.2 = bitcast i8* %.1 to [257 x i8]*
	call fastcc void @System._SStrAsg([257 x i8]* %Result.addr, i32 255, [257 x i8]* %.2)
	br label %.quit
.quit:
	ret void
}

define fastcc i8 @System.TObject.ClassNameIs(i8* %Self, i8* %Name)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8, align 1

	%Name.addr = alloca i8*, align 8
	store i8* %Name, i8** %Name.addr

	%Temp.addr = alloca [257 x i8], align 1
	%.23 = bitcast [257 x i8]* %Temp.addr to i8*
	store i8 0, i8* %.23

	%I.addr = alloca i8, align 1

	%.V1.addr = alloca i8, align 1

	store i8 0, i8* %Result.addr
	call fastcc void @System.TObject.ClassName(i8* %Self, [257 x i8]* %Temp.addr)
	store i8 0, i8* %I.addr
	%.1 = sext i8 0 to i64
	%.2 = getelementptr [257 x i8], [257 x i8]* %Temp.addr, %SizeInt 0, %SizeInt %.1
	%.3 = load i8, i8* %.2
	store i8 %.3, i8* %.V1.addr
	br label %for1.begin
for1.begin:
	%.4 = load i8, i8* %I.addr
	%.5 = load i8, i8* %.V1.addr
	%.6 = zext i8 %.4 to i32
	%.7 = zext i8 %.5 to i32
	%.8 = icmp ule i32 %.6, %.7
	br i1 %.8, label %forloop1, label %for1.br
forloop1:
	%.9 = load i8, i8* %I.addr
	%.10 = sext i8 %.9 to i64
	%.11 = getelementptr [257 x i8], [257 x i8]* %Temp.addr, %SizeInt 0, %SizeInt %.10
	%.12 = load i8, i8* %I.addr
	%.13 = sext i8 %.12 to i64
	%.14 = load i8*, i8** %Name.addr
	%.15 = sub i64 %.13, 1
	%.16 = getelementptr i8, i8* %.14, %SizeInt %.15
	%.17 = load i8, i8* %.11
	%.18 = load i8, i8* %.16
	%.19 = icmp ne i8 %.17, %.18
	br i1 %.19, label %if2.true, label %if2.false
if2.true:
	br label %.quit
if2.false:
	br label %for1.cont
for1.cont:
	%.20 = trunc i32 1 to i8
	%.21 = load i8, i8* %I.addr
	%.22 = add i8 %.21, %.20
	store i8 %.22, i8* %I.addr
	br label %for1.begin
for1.br:
	store i8 1, i8* %Result.addr
	br label %.quit
.quit:
	%.24 = load i8, i8* %Result.addr
	ret i8 %.24
}

define fastcc i8* @System.TObject.ClassParent(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%.1 = ptrtoint i8* %Self to i64
	%.2 = zext i32 -36 to i64
	%.3 = add i64 %.1, %.2
	%.4 = inttoptr i64 %.3 to i8**
	%.5 = load i8*, i8** %.4
	store i8* %.5, i8** %Result.addr
	%.6 = load i8*, i8** %Result.addr
	%.7 = icmp ne i8* %.6, null
	br i1 %.7, label %if1.true, label %if1.false
if1.true:
	%.8 = bitcast i8** %Result.addr to i8***
	%.9 = load i8**, i8*** %.8
	%.10 = load i8*, i8** %.9
	store i8* %.10, i8** %Result.addr
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	%.11 = load i8*, i8** %Result.addr
	ret i8* %.11
}

define fastcc i8* @System.TObject.ClassInfo(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%.1 = ptrtoint i8* %Self to i64
	%.2 = zext i32 -60 to i64
	%.3 = add i64 %.1, %.2
	%.4 = inttoptr i64 %.3 to i8**
	%.5 = load i8*, i8** %.4
	store i8* %.5, i8** %Result.addr
	br label %.quit
.quit:
	%.6 = load i8*, i8** %Result.addr
	ret i8* %.6
}

define fastcc i64 @System.TObject.InstanceSize(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i64, align 8

	%.1 = ptrtoint i8* %Self to i64
	%.2 = zext i32 -40 to i64
	%.3 = add i64 %.1, %.2
	%.4 = inttoptr i64 %.3 to i64*
	%.5 = load i64, i64* %.4
	store i64 %.5, i64* %Result.addr
	br label %.quit
.quit:
	%.6 = load i64, i64* %Result.addr
	ret i64 %.6
}

define fastcc i8 @System.TObject.InheritsFrom(i8* %Self, i8* %AClass)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8, align 1

	%AClass.addr = alloca i8*, align 8
	store i8* %AClass, i8** %AClass.addr

	%ClassPtr.addr = alloca i8*, align 8

	store i8* %Self, i8** %ClassPtr.addr
	br label %while1.begin
while1.begin:
	br label %expr2.1
expr2.1:
	%.1 = load i8*, i8** %ClassPtr.addr
	%.2 = icmp ne i8* %.1, null
	br i1 %.2, label %expr2.2, label %expr2.3
expr2.2:
	%.3 = load i8*, i8** %ClassPtr.addr
	%.4 = load i8*, i8** %AClass.addr
	%.5 = icmp ne i8* %.3, %.4
	br label %expr2.3
expr2.3:
	%.6 = phi i1 [ %.2, %expr2.1], [ %.5, %expr2.2 ]
	br i1 %.6, label %while1.body, label %while1.end
while1.body:
	%.7 = load i8*, i8** %ClassPtr.addr
	%.8 = getelementptr i8, i8* %.7, i32 -36
	%.9 = bitcast i8* %.8 to i8**
	%.10 = load i8*, i8** %.9
	store i8* %.10, i8** %ClassPtr.addr
	%.11 = load i8*, i8** %ClassPtr.addr
	%.12 = icmp eq i8* %.11, null
	br i1 %.12, label %if2.true, label %if2.false
if2.true:
	br label %while1.end
if2.false:
	%.13 = bitcast i8** %ClassPtr.addr to i8***
	%.14 = load i8**, i8*** %.13
	%.15 = load i8*, i8** %.14
	store i8* %.15, i8** %ClassPtr.addr
	br label %while1.end
while1.end:
	%.16 = load i8*, i8** %ClassPtr.addr
	%.17 = load i8*, i8** %AClass.addr
	%.18 = icmp eq i8* %.16, %.17
	%.19 = zext i1 %.18 to i8
	store i8 %.19, i8* %Result.addr
	br label %.quit
.quit:
	%.20 = load i8, i8* %Result.addr
	ret i8 %.20
}

define fastcc i8* @System.TObject.MethodAddress(i8* %Self, [257 x i8]* %Name.addr)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%LMethTablePtr.addr = alloca i8*, align 8

	%LMethCount.addr = alloca i16, align 2

	%LMethEntry.addr = alloca %System.MethRec*, align 8

	%LSelf.addr = alloca i8*, align 8

	store i8* null, i8** %Result.addr
	store i8* %Self, i8** %LSelf.addr
	br label %while1.begin
while1.begin:
	%.1 = icmp ne i8 0, 1
	br i1 %.1, label %while1.body, label %while1.end
while1.body:
	%.2 = load i8*, i8** %LSelf.addr
	%.3 = getelementptr i8, i8* %.2, i32 -52
	%.4 = bitcast i8* %.3 to i8**
	%.5 = load i8*, i8** %.4
	store i8* %.5, i8** %LMethTablePtr.addr
	%.6 = load i8*, i8** %LMethTablePtr.addr
	%.7 = icmp ne i8* %.6, null
	br i1 %.7, label %if2.true, label %if2.false
if2.true:
	%.8 = bitcast i8** %LMethTablePtr.addr to i16**
	%.9 = load i16*, i16** %.8
	%.10 = load i16, i16* %.9
	store i16 %.10, i16* %LMethCount.addr
	%.11 = bitcast i8** %LMethTablePtr.addr to i16**
	%.12 = sext i8 1 to i64
	%.13 = load i16*, i16** %.11
	%.14 = getelementptr i16, i16* %.13, i64 %.12
	store i16* %.14, i16** %.11
	br label %if2.end
if2.false:
	%.15 = sext i8 0 to i16
	store i16 %.15, i16* %LMethCount.addr
	br label %if2.end
if2.end:
	%.16 = load i16, i16* %LMethCount.addr
	%.17 = zext i16 %.16 to i32
	%.18 = sext i8 0 to i32
	%.19 = icmp sgt i32 %.17, %.18
	br i1 %.19, label %if3.true, label %if3.false
if3.true:
	%.20 = load i8*, i8** %LMethTablePtr.addr
	%.21 = bitcast i8* %.20 to %System.MethRec*
	store %System.MethRec* %.21, %System.MethRec** %LMethEntry.addr
	br label %while4.begin
while4.begin:
	%.22 = load i16, i16* %LMethCount.addr
	%.23 = zext i16 %.22 to i32
	%.24 = sext i8 0 to i32
	%.25 = icmp sgt i32 %.23, %.24
	br i1 %.25, label %while4.body, label %while4.end
while4.body:
	br label %expr3.1
expr3.1:
	%.26 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.27 = getelementptr %System.MethRec, %System.MethRec* %.26, %SizeInt 0, %SizeInt 10
	%.28 = bitcast i8* %.27 to i8*
	%.29 = sext i8 0 to i64
	%.30 = getelementptr [257 x i8], [257 x i8]* %Name.addr, %SizeInt 0, %SizeInt %.29
	%.31 = load i8, i8* %.28
	%.32 = load i8, i8* %.30
	%.33 = zext i8 %.31 to i32
	%.34 = zext i8 %.32 to i32
	%.35 = icmp eq i32 %.33, %.34
	br i1 %.35, label %expr3.2, label %expr3.3
expr3.2:
	%.36 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.37 = getelementptr %System.MethRec, %System.MethRec* %.36, %SizeInt 0, %SizeInt 10
	%.38 = bitcast i8* %.37 to i8*
	%.39 = bitcast i8* %.38 to [257 x i8]*
	%.40 = call fastcc i32 @System._SStrComp([257 x i8]* %.39, [257 x i8]* %Name.addr)
	%.41 = icmp eq i32 %.40, 0
	br label %expr3.3
expr3.3:
	%.42 = phi i1 [ %.35, %expr3.1], [ %.41, %expr3.2 ]
	br i1 %.42, label %if5.true, label %if5.false
if5.true:
	%.43 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.44 = getelementptr %System.MethRec, %System.MethRec* %.43, %SizeInt 0, %SizeInt 2
	%.45 = bitcast i8* %.44 to i8**
	%.46 = load i8*, i8** %.45
	store i8* %.46, i8** %Result.addr
	br label %.quit
	br label %if5.end
if5.false:
	%.47 = load i16, i16* %LMethCount.addr
	%.48 = sub i16 %.47, 1
	store i16 %.48, i16* %LMethCount.addr
	%.49 = bitcast %System.MethRec** %LMethEntry.addr to i8**
	%.50 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.51 = getelementptr %System.MethRec, %System.MethRec* %.50, %SizeInt 0, %SizeInt 0
	%.52 = bitcast i8* %.51 to i16*
	%.53 = load i8*, i8** %.49
	%.54 = load i16, i16* %.52
	%.55 = getelementptr i8, i8* %.53, i16 %.54
	%.56 = bitcast i8* %.55 to %System.MethRec*
	store %System.MethRec* %.56, %System.MethRec** %LMethEntry.addr
	br label %if5.end
if5.end:
	br label %while4.end
while4.end:
	br label %if3.false
if3.false:
	%.57 = load i8*, i8** %LSelf.addr
	%.58 = call fastcc i8* @System.TObject.ClassParent(i8* %.57)
	store i8* %.58, i8** %LSelf.addr
	%.59 = load i8*, i8** %LSelf.addr
	%.60 = icmp eq i8* %.59, null
	br i1 %.60, label %if6.true, label %if6.false
if6.true:
	br label %.quit
if6.false:
	br label %while1.end
while1.end:
	br label %.quit
.quit:
	%.61 = load i8*, i8** %Result.addr
	ret i8* %.61
}

define fastcc void @System.TObject.MethodName(i8* %Self, i8* %Address, [257 x i8]* %Result.addr)
{
	%Self.addr = alloca i8*, align 8

	%Address.addr = alloca i8*, align 8
	store i8* %Address, i8** %Address.addr

	%LMethTablePtr.addr = alloca i8*, align 8

	%LMethCount.addr = alloca i16, align 2

	%LMethEntry.addr = alloca %System.MethRec*, align 8

	%LSelf.addr = alloca i8*, align 8

	call fastcc void @System._SStrClr([257 x i8]* %Result.addr)
	store i8* %Self, i8** %LSelf.addr
	br label %while1.begin
while1.begin:
	%.1 = icmp ne i8 0, 1
	br i1 %.1, label %while1.body, label %while1.end
while1.body:
	%.2 = load i8*, i8** %LSelf.addr
	%.3 = getelementptr i8, i8* %.2, i32 -52
	%.4 = bitcast i8* %.3 to i8**
	%.5 = load i8*, i8** %.4
	store i8* %.5, i8** %LMethTablePtr.addr
	%.6 = load i8*, i8** %LMethTablePtr.addr
	%.7 = icmp ne i8* %.6, null
	br i1 %.7, label %if2.true, label %if2.false
if2.true:
	%.8 = bitcast i8** %LMethTablePtr.addr to i16**
	%.9 = load i16*, i16** %.8
	%.10 = load i16, i16* %.9
	store i16 %.10, i16* %LMethCount.addr
	%.11 = bitcast i8** %LMethTablePtr.addr to i16**
	%.12 = sext i8 1 to i64
	%.13 = load i16*, i16** %.11
	%.14 = getelementptr i16, i16* %.13, i64 %.12
	store i16* %.14, i16** %.11
	br label %if2.end
if2.false:
	%.15 = sext i8 0 to i16
	store i16 %.15, i16* %LMethCount.addr
	br label %if2.end
if2.end:
	%.16 = load i16, i16* %LMethCount.addr
	%.17 = zext i16 %.16 to i32
	%.18 = sext i8 0 to i32
	%.19 = icmp sgt i32 %.17, %.18
	br i1 %.19, label %if3.true, label %if3.false
if3.true:
	%.20 = load i8*, i8** %LMethTablePtr.addr
	%.21 = bitcast i8* %.20 to %System.MethRec*
	store %System.MethRec* %.21, %System.MethRec** %LMethEntry.addr
	br label %while4.begin
while4.begin:
	%.22 = load i16, i16* %LMethCount.addr
	%.23 = zext i16 %.22 to i32
	%.24 = sext i8 0 to i32
	%.25 = icmp sgt i32 %.23, %.24
	br i1 %.25, label %while4.body, label %while4.end
while4.body:
	%.26 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.27 = getelementptr %System.MethRec, %System.MethRec* %.26, %SizeInt 0, %SizeInt 2
	%.28 = bitcast i8* %.27 to i8**
	%.29 = load i8*, i8** %.28
	%.30 = load i8*, i8** %Address.addr
	%.31 = icmp eq i8* %.29, %.30
	br i1 %.31, label %if5.true, label %if5.false
if5.true:
	%.32 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.33 = getelementptr %System.MethRec, %System.MethRec* %.32, %SizeInt 0, %SizeInt 10
	%.34 = bitcast i8* %.33 to i8*
	%.35 = bitcast i8* %.34 to [257 x i8]*
	call fastcc void @System._SStrAsg([257 x i8]* %Result.addr, i32 255, [257 x i8]* %.35)
	br label %.quit
	br label %if5.end
if5.false:
	%.36 = load i16, i16* %LMethCount.addr
	%.37 = sub i16 %.36, 1
	store i16 %.37, i16* %LMethCount.addr
	%.38 = bitcast %System.MethRec** %LMethEntry.addr to i8**
	%.39 = load %System.MethRec*, %System.MethRec** %LMethEntry.addr
	%.40 = getelementptr %System.MethRec, %System.MethRec* %.39, %SizeInt 0, %SizeInt 0
	%.41 = bitcast i8* %.40 to i16*
	%.42 = load i8*, i8** %.38
	%.43 = load i16, i16* %.41
	%.44 = getelementptr i8, i8* %.42, i16 %.43
	%.45 = bitcast i8* %.44 to %System.MethRec*
	store %System.MethRec* %.45, %System.MethRec** %LMethEntry.addr
	br label %if5.end
if5.end:
	br label %while4.end
while4.end:
	br label %if3.false
if3.false:
	%.46 = load i8*, i8** %LSelf.addr
	%.47 = call fastcc i8* @System.TObject.ClassParent(i8* %.46)
	store i8* %.47, i8** %LSelf.addr
	%.48 = load i8*, i8** %LSelf.addr
	%.49 = icmp eq i8* %.48, null
	br i1 %.49, label %if6.true, label %if6.false
if6.true:
	br label %.quit
if6.false:
	br label %while1.end
while1.end:
	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System.TObject.FieldAddress(i8* %Self, [257 x i8]* %Name.addr)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%LFieldTablePtr.addr = alloca i8*, align 8

	%LFldCount.addr = alloca i16, align 2

	%LName.addr = alloca [257 x i8]*, align 8

	%LClass.addr = alloca i8*, align 8

	store i8* null, i8** %Result.addr
	%.1 = bitcast i8* %Self to i8**
	%.2 = load i8*, i8** %.1
	store i8* %.2, i8** %LClass.addr
	br label %while1.begin
while1.begin:
	%.3 = icmp ne i8 0, 1
	br i1 %.3, label %while1.body, label %while1.end
while1.body:
	%.4 = load i8*, i8** %LClass.addr
	%.5 = getelementptr i8, i8* %.4, i32 -56
	%.6 = bitcast i8* %.5 to i8**
	%.7 = load i8*, i8** %.6
	store i8* %.7, i8** %LFieldTablePtr.addr
	%.8 = load i8*, i8** %LFieldTablePtr.addr
	%.9 = icmp ne i8* %.8, null
	br i1 %.9, label %if2.true, label %if2.false
if2.true:
	%.10 = bitcast i8** %LFieldTablePtr.addr to i16**
	%.11 = load i16*, i16** %.10
	%.12 = load i16, i16* %.11
	store i16 %.12, i16* %LFldCount.addr
	%.13 = bitcast i8** %LFieldTablePtr.addr to i16**
	%.14 = sext i8 1 to i64
	%.15 = load i16*, i16** %.13
	%.16 = getelementptr i16, i16* %.15, i64 %.14
	store i16* %.16, i16** %.13
	%.17 = bitcast i8** %LFieldTablePtr.addr to i8***
	%.18 = sext i8 1 to i64
	%.19 = load i8**, i8*** %.17
	%.20 = getelementptr i8*, i8** %.19, i64 %.18
	store i8** %.20, i8*** %.17
	br label %if2.end
if2.false:
	%.21 = sext i8 0 to i16
	store i16 %.21, i16* %LFldCount.addr
	br label %if2.end
if2.end:
	%.22 = load i16, i16* %LFldCount.addr
	%.23 = zext i16 %.22 to i32
	%.24 = sext i8 0 to i32
	%.25 = icmp sgt i32 %.23, %.24
	br i1 %.25, label %if3.true, label %if3.false
if3.true:
	br label %while4.begin
while4.begin:
	%.26 = load i16, i16* %LFldCount.addr
	%.27 = zext i16 %.26 to i32
	%.28 = sext i8 0 to i32
	%.29 = icmp sgt i32 %.27, %.28
	br i1 %.29, label %while4.body, label %while4.end
while4.body:
	%.30 = load i8*, i8** %LFieldTablePtr.addr
	%.31 = getelementptr i8, i8* %.30, i8 2
	%.32 = getelementptr i8, i8* %.31, i8 4
	%.33 = bitcast i8* %.32 to [257 x i8]*
	store [257 x i8]* %.33, [257 x i8]** %LName.addr
	br label %expr4.1
expr4.1:
	%.34 = sext i8 0 to i64
	%.35 = load [257 x i8]*, [257 x i8]** %LName.addr
	%.36 = getelementptr [257 x i8], [257 x i8]* %.35, %SizeInt 0, %SizeInt %.34
	%.37 = sext i8 0 to i64
	%.38 = getelementptr [257 x i8], [257 x i8]* %Name.addr, %SizeInt 0, %SizeInt %.37
	%.39 = load i8, i8* %.36
	%.40 = load i8, i8* %.38
	%.41 = icmp eq i8 %.39, %.40
	br i1 %.41, label %expr4.2, label %expr4.3
expr4.2:
	%.42 = load [257 x i8]*, [257 x i8]** %LName.addr
	%.43 = call fastcc i32 @System._SStrComp([257 x i8]* %.42, [257 x i8]* %Name.addr)
	%.44 = icmp eq i32 %.43, 0
	br label %expr4.3
expr4.3:
	%.45 = phi i1 [ %.41, %expr4.1], [ %.44, %expr4.2 ]
	br i1 %.45, label %if5.true, label %if5.false
if5.true:
	%.46 = bitcast i8** %LFieldTablePtr.addr to i32**
	%.47 = load i32*, i32** %.46
	%.48 = load i32, i32* %.47
	%.49 = getelementptr i8, i8* %Self, i32 %.48
	store i8* %.49, i8** %Result.addr
	br label %.quit
	br label %if5.end
if5.false:
	%.50 = load i16, i16* %LFldCount.addr
	%.51 = sub i16 %.50, 1
	store i16 %.51, i16* %LFldCount.addr
	%.52 = sext i8 0 to i64
	%.53 = load [257 x i8]*, [257 x i8]** %LName.addr
	%.54 = getelementptr [257 x i8], [257 x i8]* %.53, %SizeInt 0, %SizeInt %.52
	%.55 = load i8, i8* %.54
	%.56 = sext i8 6 to i32
	%.57 = zext i8 %.55 to i32
	%.58 = add i32 %.56, %.57
	%.59 = sext i8 1 to i32
	%.60 = add i32 %.58, %.59
	%.61 = sext i32 %.60 to i64
	%.62 = load i8*, i8** %LFieldTablePtr.addr
	%.63 = getelementptr i8, i8* %.62, i64 %.61
	store i8* %.63, i8** %LFieldTablePtr.addr
	br label %if5.end
if5.end:
	br label %while4.end
while4.end:
	br label %if3.false
if3.false:
	%.64 = load i8*, i8** %LClass.addr
	%.65 = call fastcc i8* @System.TObject.ClassParent(i8* %.64)
	store i8* %.65, i8** %LClass.addr
	%.66 = load i8*, i8** %LClass.addr
	%.67 = icmp eq i8* %.66, null
	br i1 %.67, label %if6.true, label %if6.false
if6.true:
	br label %.quit
if6.false:
	br label %while1.end
while1.end:
	br label %.quit
.quit:
	%.68 = load i8*, i8** %Result.addr
	ret i8* %.68
}

define fastcc i8 @System.TObject.GetInterface(i8* %Self, %System.TGUID* %IID.addr, i8* %Obj.addr)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8, align 1

	%InterfaceEntry.addr = alloca %System.TInterfaceEntry*, align 8

	%.1 = bitcast i8* %Obj.addr to i8**
	store i8* null, i8** %.1
	%.2 = bitcast i8* %Self to i8**
	%.3 = load i8*, i8** %.2
	%.4 = call fastcc %System.TInterfaceEntry* @System.TObject.GetInterfaceEntry(i8* %.3, %System.TGUID* %IID.addr)
	store %System.TInterfaceEntry* %.4, %System.TInterfaceEntry** %InterfaceEntry.addr
	%.5 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %InterfaceEntry.addr
	%.6 = bitcast i8* null to %System.TInterfaceEntry*
	%.7 = icmp ne %System.TInterfaceEntry* %.5, %.6
	br i1 %.7, label %if1.true, label %if1.false
if1.true:
	%.8 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %InterfaceEntry.addr
	%.9 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.8, %SizeInt 0, %SizeInt 24
	%.10 = bitcast i8* %.9 to i32*
	%.11 = load i32, i32* %.10
	%.12 = sext i8 0 to i32
	%.13 = icmp ne i32 %.11, %.12
	br i1 %.13, label %if2.true, label %if2.false
if2.true:
	%.14 = bitcast i8* %Obj.addr to i8**
	%.15 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %InterfaceEntry.addr
	%.16 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.15, %SizeInt 0, %SizeInt 24
	%.17 = bitcast i8* %.16 to i32*
	%.18 = load i32, i32* %.17
	%.19 = getelementptr i8, i8* %Self, i32 %.18
	store i8* %.19, i8** %.14
	%.20 = bitcast i8* %Obj.addr to i8**
	%.21 = load i8*, i8** %.20
	%.22 = icmp ne i8* %.21, null
	br i1 %.22, label %if3.true, label %if3.false
if3.true:
	%.23 = bitcast i8* %Obj.addr to i8***
	%.24 = load i8**, i8*** %.23
	%.25 = bitcast i8** %.24 to i8***
	%.26 = load i8**, i8*** %.25
	%.27 = getelementptr i8*, i8** %.26, %SizeInt 1
	%.28 = load i8*, i8** %.27
	%.29 = bitcast i8* %.28 to i32 (i8*)*
	%.30 = bitcast i8** %.24 to i8*
	%.31 = call cc 64 i32 %.29(i8* %.30)
	br label %if3.false
if3.false:
	br label %if2.end
if2.false:
	%.32 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %InterfaceEntry.addr
	%.33 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.32, %SizeInt 0, %SizeInt 28
	%.34 = bitcast i8* %.33 to i32*
	%.35 = load i32, i32* %.34
	%.36 = bitcast i8* %Obj.addr to i8***
	call fastcc void @System.InvokeImplGetter(i8* %Self, i32 %.35, i8*** %.36)
	br label %if2.end
if2.end:
	br label %if1.false
if1.false:
	%.37 = bitcast i8* %Obj.addr to i8**
	%.38 = load i8*, i8** %.37
	%.39 = icmp ne i8* %.38, null
	%.40 = zext i1 %.39 to i8
	store i8 %.40, i8* %Result.addr
	br label %.quit
.quit:
	%.41 = load i8, i8* %Result.addr
	ret i8 %.41
}

define fastcc %System.TInterfaceEntry* @System.TObject.GetInterfaceEntry(i8* %Self, %System.TGUID* %IID.addr)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca %System.TInterfaceEntry*, align 8

	%ClassPtr.addr = alloca i8*, align 8

	%IntfTable.addr = alloca %System.TInterfaceTable*, align 8

	%I.addr = alloca i32, align 4

	%.V1.addr = alloca i32, align 4

	store i8* %Self, i8** %ClassPtr.addr
	br label %while1.begin
while1.begin:
	%.1 = load i8*, i8** %ClassPtr.addr
	%.2 = icmp ne i8* %.1, null
	br i1 %.2, label %while1.body, label %while1.end
while1.body:
	%.3 = load i8*, i8** %ClassPtr.addr
	%.4 = call fastcc %System.TInterfaceTable* @System.TObject.GetInterfaceTable(i8* %.3)
	store %System.TInterfaceTable* %.4, %System.TInterfaceTable** %IntfTable.addr
	%.5 = load %System.TInterfaceTable*, %System.TInterfaceTable** %IntfTable.addr
	%.6 = bitcast i8* null to %System.TInterfaceTable*
	%.7 = icmp ne %System.TInterfaceTable* %.5, %.6
	br i1 %.7, label %if2.true, label %if2.false
if2.true:
	%.8 = sext i8 0 to i32
	store i32 %.8, i32* %I.addr
	%.9 = load %System.TInterfaceTable*, %System.TInterfaceTable** %IntfTable.addr
	%.10 = getelementptr %System.TInterfaceTable, %System.TInterfaceTable* %.9, %SizeInt 0, %SizeInt 0
	%.11 = bitcast i8* %.10 to i32*
	%.12 = load i32, i32* %.11
	%.13 = sext i8 1 to i32
	%.14 = sub i32 %.12, %.13
	store i32 %.14, i32* %.V1.addr
	br label %for3.begin
for3.begin:
	%.15 = load i32, i32* %I.addr
	%.16 = load i32, i32* %.V1.addr
	%.17 = icmp sle i32 %.15, %.16
	br i1 %.17, label %forloop1, label %for3.br
forloop1:
	%.18 = load i32, i32* %I.addr
	%.19 = sext i32 %.18 to i64
	%.20 = load %System.TInterfaceTable*, %System.TInterfaceTable** %IntfTable.addr
	%.21 = getelementptr %System.TInterfaceTable, %System.TInterfaceTable* %.20, %SizeInt 0, %SizeInt 4
	%.22 = bitcast i8* %.21 to [10000 x %System.TInterfaceEntry]*
	%.23 = getelementptr [10000 x %System.TInterfaceEntry], [10000 x %System.TInterfaceEntry]* %.22, %SizeInt 0, %SizeInt %.19
	%.24 = bitcast %System.TInterfaceEntry* %.23 to i8*
	%.25 = bitcast i8* %.24 to %System.TInterfaceEntry*
	store %System.TInterfaceEntry* %.25, %System.TInterfaceEntry** %Result.addr
	br label %expr5.1
expr5.1:
	br label %expr6.4
expr6.4:
	br label %expr7.7
expr7.7:
	%.26 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %Result.addr
	%.27 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.26, %SizeInt 0, %SizeInt 0
	%.28 = bitcast i8* %.27 to %System.TGUID*
	%.29 = getelementptr %System.TGUID, %System.TGUID* %.28, %SizeInt 0, %SizeInt 0
	%.30 = bitcast i8* %.29 to i32*
	%.31 = getelementptr %System.TGUID, %System.TGUID* %IID.addr, %SizeInt 0, %SizeInt 0
	%.32 = bitcast i8* %.31 to i32*
	%.33 = load i32, i32* %.30
	%.34 = load i32, i32* %.32
	%.35 = icmp eq i32 %.33, %.34
	br i1 %.35, label %expr7.8, label %expr7.9
expr7.8:
	%.36 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %Result.addr
	%.37 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.36, %SizeInt 0, %SizeInt 0
	%.38 = bitcast i8* %.37 to %System.TGUID*
	%.39 = getelementptr %System.TGUID, %System.TGUID* %.38, %SizeInt 0, %SizeInt 4
	%.40 = bitcast i8* %.39 to i16*
	%.41 = getelementptr %System.TGUID, %System.TGUID* %IID.addr, %SizeInt 0, %SizeInt 4
	%.42 = bitcast i8* %.41 to i16*
	%.43 = load i16, i16* %.40
	%.44 = load i16, i16* %.42
	%.45 = zext i16 %.43 to i32
	%.46 = zext i16 %.44 to i32
	%.47 = icmp eq i32 %.45, %.46
	br label %expr7.9
expr7.9:
	%.48 = phi i1 [ %.35, %expr7.7], [ %.47, %expr7.8 ]
	br i1 %.48, label %expr6.5, label %expr6.6
expr6.5:
	%.49 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %Result.addr
	%.50 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.49, %SizeInt 0, %SizeInt 0
	%.51 = bitcast i8* %.50 to %System.TGUID*
	%.52 = getelementptr %System.TGUID, %System.TGUID* %.51, %SizeInt 0, %SizeInt 6
	%.53 = bitcast i8* %.52 to i16*
	%.54 = getelementptr %System.TGUID, %System.TGUID* %IID.addr, %SizeInt 0, %SizeInt 6
	%.55 = bitcast i8* %.54 to i16*
	%.56 = load i16, i16* %.53
	%.57 = load i16, i16* %.55
	%.58 = zext i16 %.56 to i32
	%.59 = zext i16 %.57 to i32
	%.60 = icmp eq i32 %.58, %.59
	br label %expr6.6
expr6.6:
	%.61 = phi i1 [ %.48, %expr7.9], [ %.60, %expr6.5 ]
	br i1 %.61, label %expr5.2, label %expr5.3
expr5.2:
	%.62 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %Result.addr
	%.63 = getelementptr %System.TInterfaceEntry, %System.TInterfaceEntry* %.62, %SizeInt 0, %SizeInt 0
	%.64 = bitcast i8* %.63 to %System.TGUID*
	%.65 = getelementptr %System.TGUID, %System.TGUID* %.64, %SizeInt 0, %SizeInt 8
	%.66 = bitcast i8* %.65 to [8 x i8]*
	%.67 = bitcast [8 x i8]* %.66 to i64*
	%.68 = getelementptr %System.TGUID, %System.TGUID* %IID.addr, %SizeInt 0, %SizeInt 8
	%.69 = bitcast i8* %.68 to [8 x i8]*
	%.70 = bitcast [8 x i8]* %.69 to i64*
	%.71 = load i64, i64* %.67
	%.72 = load i64, i64* %.70
	%.73 = icmp eq i64 %.71, %.72
	br label %expr5.3
expr5.3:
	%.74 = phi i1 [ %.61, %expr6.6], [ %.73, %expr5.2 ]
	br i1 %.74, label %if4.true, label %if4.false
if4.true:
	br label %.quit
if4.false:
	br label %for3.cont
for3.cont:
	%.75 = load i32, i32* %I.addr
	%.76 = add i32 %.75, 1
	store i32 %.76, i32* %I.addr
	br label %for3.begin
for3.br:
	br label %if2.false
if2.false:
	%.77 = load i8*, i8** %ClassPtr.addr
	%.78 = call fastcc i8* @System.TObject.ClassParent(i8* %.77)
	store i8* %.78, i8** %ClassPtr.addr
	br label %while1.end
while1.end:
	%.79 = bitcast i8* null to %System.TInterfaceEntry*
	store %System.TInterfaceEntry* %.79, %System.TInterfaceEntry** %Result.addr
	br label %.quit
.quit:
	%.80 = load %System.TInterfaceEntry*, %System.TInterfaceEntry** %Result.addr
	ret %System.TInterfaceEntry* %.80
}

define fastcc %System.TInterfaceTable* @System.TObject.GetInterfaceTable(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca %System.TInterfaceTable*, align 8

	%.1 = ptrtoint i8* %Self to i64
	%.2 = zext i32 -72 to i64
	%.3 = add i64 %.1, %.2
	%.4 = inttoptr i64 %.3 to i8**
	%.5 = load i8*, i8** %.4
	%.6 = bitcast i8* %.5 to %System.TInterfaceTable*
	store %System.TInterfaceTable* %.6, %System.TInterfaceTable** %Result.addr
	br label %.quit
.quit:
	%.7 = load %System.TInterfaceTable*, %System.TInterfaceTable** %Result.addr
	ret %System.TInterfaceTable* %.7
}

define fastcc i32 @System.TObject.SafeCallException(i8* %Self, i8* %ExceptObject, i8* %ExceptAddr)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i32, align 4

	store i32 -2147418113, i32* %Result.addr
	br label %.quit
.quit:
	%.1 = load i32, i32* %Result.addr
	ret i32 %.1
}

define fastcc void @System.TObject.AfterConstruction(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	br label %.quit
.quit:
	ret void
}

define fastcc void @System.TObject.BeforeDestruction(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	br label %.quit
.quit:
	ret void
}

define fastcc void @System.TObject.Dispatch(i8* %Self, i8* %Message.addr)
{
	%Self.addr = alloca i8*, align 8

	%MsgID.addr = alloca i16, align 2

	%Addr.addr = alloca i8*, align 8

	%M.addr = alloca [2 x i8*], align 16

	%.1 = bitcast i8* %Message.addr to %System.TDispatchMessage*
	%.2 = getelementptr %System.TDispatchMessage, %System.TDispatchMessage* %.1, %SizeInt 0, %SizeInt 0
	%.3 = bitcast i8* %.2 to i16*
	%.4 = load i16, i16* %.3
	store i16 %.4, i16* %MsgID.addr
	br label %expr8.1
expr8.1:
	%.5 = load i16, i16* %MsgID.addr
	%.6 = zext i16 %.5 to i32
	%.7 = sext i8 0 to i32
	%.8 = icmp ne i32 %.6, %.7
	br i1 %.8, label %expr8.2, label %expr8.3
expr8.2:
	%.9 = load i16, i16* %MsgID.addr
	%.10 = zext i16 %.9 to i32
	%.11 = zext i16 49152 to i32
	%.12 = icmp ult i32 %.10, %.11
	br label %expr8.3
expr8.3:
	%.13 = phi i1 [ %.8, %expr8.1], [ %.12, %expr8.2 ]
	br i1 %.13, label %if1.true, label %if1.false
if1.true:
	%.14 = bitcast i8* %Self to i8**
	%.15 = load i8*, i8** %.14
	%.16 = load i16, i16* %MsgID.addr
	%.17 = call fastcc i8* @System.GetDynaMethod(i8* %.15, i16 %.16)
	store i8* %.17, i8** %Addr.addr
	%.18 = load i8*, i8** %Addr.addr
	%.19 = icmp ne i8* %.18, null
	br i1 %.19, label %if2.true, label %if2.false
if2.true:
	%.20 = bitcast [2 x i8*]* %M.addr to %System.TMethod*
	%.21 = getelementptr %System.TMethod, %System.TMethod* %.20, %SizeInt 0, %SizeInt 8
	%.22 = bitcast i8* %.21 to i8**
	store i8* %Self, i8** %.22
	%.23 = bitcast [2 x i8*]* %M.addr to %System.TMethod*
	%.24 = getelementptr %System.TMethod, %System.TMethod* %.23, %SizeInt 0, %SizeInt 0
	%.25 = bitcast i8* %.24 to i8**
	%.26 = load i8*, i8** %Addr.addr
	store i8* %.26, i8** %.25
	%.27 = getelementptr [2 x i8*], [2 x i8*]* %M.addr, i32 0, i32 1
	%.28 = load i8*, i8** %.27
	%.29 = getelementptr [2 x i8*], [2 x i8*]* %M.addr, i32 0, i32 0
	%.30 = load i8*, i8** %.29
	%.31 = bitcast i8* %.30 to void (i8*, i8*)*
	%.32 = bitcast i8* %Message.addr to i8*
	call fastcc void %.31(i8* %.28, i8* %.32)
	br label %if2.end
if2.false:
	%.33 = bitcast i8* %Self to i8***
	%.34 = load i8**, i8*** %.33
	%.35 = getelementptr i8*, i8** %.34, %SizeInt -4
	%.36 = load i8*, i8** %.35
	%.37 = bitcast i8* %.36 to void (i8*, i8*)*
	%.38 = bitcast i8* %Message.addr to i8*
	call fastcc void %.37(i8* %Self, i8* %.38)
	br label %if2.end
if2.end:
	br label %if1.end
if1.false:
	%.39 = bitcast i8* %Self to i8***
	%.40 = load i8**, i8*** %.39
	%.41 = getelementptr i8*, i8** %.40, %SizeInt -4
	%.42 = load i8*, i8** %.41
	%.43 = bitcast i8* %.42 to void (i8*, i8*)*
	%.44 = bitcast i8* %Message.addr to i8*
	call fastcc void %.43(i8* %Self, i8* %.44)
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.TObject.DefaultHandler(i8* %Self, i8* %Message.addr)
{
	%Self.addr = alloca i8*, align 8

	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System.TObject.NewInstance(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	%Result.addr = alloca i8*, align 8

	%.1 = call fastcc i64 @System.TObject.InstanceSize(i8* %Self)
	%.2 = trunc i64 %.1 to i32
	%.3 = call fastcc i8* @System._GetMem(i32 %.2)
	%.4 = call fastcc i8* @System.TObject.InitInstance(i8* %Self, i8* %.3)
	store i8* %.4, i8** %Result.addr
	br label %.quit
.quit:
	%.5 = load i8*, i8** %Result.addr
	ret i8* %.5
}

define fastcc void @System.TObject.FreeInstance(i8* %Self)
{
	%Self.addr = alloca i8*, align 8

	call fastcc void @System.TObject.CleanupInstance(i8* %Self)
	call fastcc void @System._FreeMem(i8* %Self)
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.TObject.Destroy(i8* %Self, i8 %.outterMost)
{
	%Self.addr = alloca i8*, align 8

	br label %.quit
.quit:
	ret void
}

define fastcc void @System.FillChar(i8* %Dest.addr, i64 %Count, i8 %Value)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.Move(i8* %Source.addr, i8* %Dest.addr, i64 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i32 @System.InterLockedIncrement(i32* %dest.addr)
{
	%Result.addr = alloca i32, align 4

	br label %.quit
.quit:
	%.1 = load i32, i32* %Result.addr
	ret i32 %.1
}

define fastcc i64 @System.InterLockedIncrement64(i64* %dest.addr)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc i32 @System.InterLockedDecrement(i32* %dest.addr)
{
	%Result.addr = alloca i32, align 4

	br label %.quit
.quit:
	%.1 = load i32, i32* %Result.addr
	ret i32 %.1
}

define fastcc i64 @System.InterLockedDecrement64(i64* %dest.addr)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc i32 @System.InterLockedCompareExchange(i32* %dest.addr, i32 %exchange, i32 %comparand)
{
	%Result.addr = alloca i32, align 4

	br label %.quit
.quit:
	%.1 = load i32, i32* %Result.addr
	ret i32 %.1
}

define fastcc i64 @System.InterLockedCompareExchange64(i64* %dest.addr, i64 %exchange, i64 %comparand)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc i32 @System.InterLockedExchange(i32* %dest.addr, i32 %value)
{
	%Result.addr = alloca i32, align 4

	br label %.quit
.quit:
	%.1 = load i32, i32* %Result.addr
	ret i32 %.1
}

define fastcc i64 @System.InterLockedExchange64(i64* %dest.addr, i64 %value)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc i32 @System.InterLockedExchangeAdd(i32* %dest.addr, i32 %value)
{
	%Result.addr = alloca i32, align 4

	br label %.quit
.quit:
	%.1 = load i32, i32* %Result.addr
	ret i32 %.1
}

define fastcc i64 @System.InterLockedExchangeAdd64(i64* %dest.addr, i64 %value)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc void @System._CrtExit(i32 %code)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System._GetMem(i32 %Size)
{
	%Result.addr = alloca i8*, align 8

	%Size.addr = alloca i32, align 4
	store i32 %Size, i32* %Size.addr

	%.1 = load i32, i32* %Size.addr
	%.2 = sext i32 %.1 to i64
	%.3 = tail call noalias i8* @malloc(i64 %.2) nounwind
	store i8* %.3, i8** %Result.addr
	br label %.quit
.quit:
	%.4 = load i8*, i8** %Result.addr
	ret i8* %.4
}

define fastcc void @System._FreeMem(i8* %P)
{
	%P.addr = alloca i8*, align 8
	store i8* %P, i8** %P.addr

	%.1 = load i8*, i8** %P.addr
	tail call void @free(i8* %.1) nounwind
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._IntOverflow()
{
	call fastcc void @System.Error(i8 5)
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._OutOfRange()
{
	call fastcc void @System.Error(i8 4)
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._IOCheck()
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SafecallCheck(i32 %hr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._RaiseExcept(i8* %exobj)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Rethrow(i8* %exobj)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._FreeExceptObject(i8* %exobj)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._HandleSafecallExcept(i8* %Instance, i8* %ExceptObject)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i32 @System._InternalHandleSafecall(i8* %Instance, i8* %ExceptObject)
{
	%Result.addr = alloca i32, align 4

	%Instance.addr = alloca i8*, align 8
	store i8* %Instance, i8** %Instance.addr

	%ExceptObject.addr = alloca i8*, align 8
	store i8* %ExceptObject, i8** %ExceptObject.addr

	%.1 = load i8*, i8** %Instance.addr
	%.2 = icmp eq i8* %.1, null
	br i1 %.2, label %if1.true, label %if1.false
if1.true:
	store i32 -2147418113, i32* %Result.addr
	br label %if1.end
if1.false:
	%.3 = load i8*, i8** %Instance.addr
	%.4 = bitcast i8* %.3 to i8***
	%.5 = load i8**, i8*** %.4
	%.6 = getelementptr i8*, i8** %.5, %SizeInt -8
	%.7 = load i8*, i8** %.6
	%.8 = bitcast i8* %.7 to i32 (i8*, i8*, i8*)*
	%.9 = load i8*, i8** %ExceptObject.addr
	%.10 = call fastcc i32 %.8(i8* %.3, i8* %.9, i8* null)
	store i32 %.10, i32* %Result.addr
	br label %if1.end
if1.end:
	%.11 = load i8*, i8** %ExceptObject.addr
	call fastcc void @System.TObject.Free(i8* %.11)
	br label %.quit
.quit:
	%.12 = load i32, i32* %Result.addr
	ret i32 %.12
}

define fastcc void @System._HandleCtorExcept(i8* %E, i8* %Instance, i8 %Flag)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._HandleFinally(i8* %ExceptObject)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Terminated()
{
	br label %.quit
.quit:
	ret void
}

define fastcc i8 @System._IsClass(i8* %Child, i8* %Parent)
{
	%Result.addr = alloca i8, align 1

	%Child.addr = alloca i8*, align 8
	store i8* %Child, i8** %Child.addr

	%Parent.addr = alloca i8*, align 8
	store i8* %Parent, i8** %Parent.addr

	br label %expr9.1
expr9.1:
	%.1 = load i8*, i8** %Child.addr
	%.2 = icmp ne i8* %.1, null
	br i1 %.2, label %expr9.2, label %expr9.3
expr9.2:
	%.3 = load i8*, i8** %Child.addr
	%.4 = bitcast i8* %.3 to i8**
	%.5 = load i8*, i8** %.4
	%.6 = load i8*, i8** %Parent.addr
	%.7 = call fastcc i8 @System.TObject.InheritsFrom(i8* %.5, i8* %.6)
	%.8 = icmp ne i8 0, %.7
	br label %expr9.3
expr9.3:
	%.9 = phi i1 [ %.2, %expr9.1], [ %.8, %expr9.2 ]
	%.10 = zext i1 %.9 to i8
	store i8 %.10, i8* %Result.addr
	br label %.quit
.quit:
	%.11 = load i8, i8* %Result.addr
	ret i8 %.11
}

define fastcc i8* @System._AsClass(i8* %Child, i8* %Parent)
{
	%Result.addr = alloca i8*, align 8

	%Child.addr = alloca i8*, align 8
	store i8* %Child, i8** %Child.addr

	%Parent.addr = alloca i8*, align 8
	store i8* %Parent, i8** %Parent.addr

	%.1 = load i8*, i8** %Child.addr
	store i8* %.1, i8** %Result.addr
	%.2 = load i8*, i8** %Child.addr
	%.3 = load i8*, i8** %Parent.addr
	%.4 = call fastcc i8 @System._IsClass(i8* %.2, i8* %.3)
	; not op
	%.5 = icmp ne i8 %.4, 0
	%.6 = select i1 %.5, i8 0, i8 1
	%.7 = icmp ne i8 0, %.6
	br i1 %.7, label %if1.true, label %if1.false
if1.true:
	call fastcc void @System.Error(i8 10)
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	%.8 = load i8*, i8** %Result.addr
	ret i8* %.8
}

define fastcc i8 @System._IntfIsClass(i8** %Intf, i8* %Parent)
{
	%Result.addr = alloca i8, align 1

	%Intf.addr = alloca i8**, align 8
	store i8** %Intf, i8*** %Intf.addr

	%Parent.addr = alloca i8*, align 8
	store i8* %Parent, i8** %Parent.addr

	%.1 = load i8**, i8*** %Intf.addr
	%.2 = load i8*, i8** %Parent.addr
	%.3 = call fastcc i8* @System._SafeIntfAsClass(i8** %.1, i8* %.2)
	%.4 = icmp ne i8* %.3, null
	%.5 = zext i1 %.4 to i8
	store i8 %.5, i8* %Result.addr
	br label %.quit
.quit:
	%.6 = load i8, i8* %Result.addr
	ret i8 %.6
}

define fastcc i8* @System._IntfAsClass(i8** %Intf, i8* %Parent)
{
	%Result.addr = alloca i8*, align 8

	store i8* null, i8** %Result.addr
	br label %.quit
.quit:
	%.1 = load i8*, i8** %Result.addr
	ret i8* %.1
}

define fastcc i8* @System._SafeIntfAsClass(i8** %Intf, i8* %Parent)
{
	%Result.addr = alloca i8*, align 8

	store i8* null, i8** %Result.addr
	br label %.quit
.quit:
	%.1 = load i8*, i8** %Result.addr
	ret i8* %.1
}





define fastcc i64 @System._Round(double %v)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc i64 @System._Trunc(double %v)
{
	%Result.addr = alloca i64, align 8

	br label %.quit
.quit:
	%.1 = load i64, i64* %Result.addr
	ret i64 %.1
}

define fastcc void @System._AStrClr(i8** %S.addr)
{
	%P.addr = alloca %System.AnsiStrRec*, align 8

	%.1 = load i8*, i8** %S.addr
	%.2 = icmp eq i8* %.1, null
	br i1 %.2, label %if1.true, label %if1.false
if1.true:
	br label %.quit
if1.false:
	%.3 = bitcast i8** %S.addr to i64*
	%.4 = load i64, i64* %.3
	%.5 = sext i8 16 to i64
	%.6 = sub i64 %.4, %.5
	%.7 = inttoptr i64 %.6 to i8*
	%.8 = bitcast i8* %.7 to %System.AnsiStrRec*
	store %System.AnsiStrRec* %.8, %System.AnsiStrRec** %P.addr
	store i8* null, i8** %S.addr
	%.9 = load %System.AnsiStrRec*, %System.AnsiStrRec** %P.addr
	%.10 = getelementptr %System.AnsiStrRec, %System.AnsiStrRec* %.9, %SizeInt 0, %SizeInt 4
	%.11 = bitcast i8* %.10 to i32*
	%.12 = load i32, i32* %.11
	%.13 = sext i8 0 to i32
	%.14 = icmp sgt i32 %.12, %.13
	br i1 %.14, label %if2.true, label %if2.false
if2.true:
	%.15 = load %System.AnsiStrRec*, %System.AnsiStrRec** %P.addr
	%.16 = getelementptr %System.AnsiStrRec, %System.AnsiStrRec* %.15, %SizeInt 0, %SizeInt 4
	%.17 = bitcast i8* %.16 to i32*
	%.18 = call fastcc i32 @System.InterLockedDecrement(i32* %.17)
	%.19 = sext i8 0 to i32
	%.20 = icmp eq i32 %.18, %.19
	br i1 %.20, label %if3.true, label %if3.false
if3.true:
	%.21 = load %System.AnsiStrRec*, %System.AnsiStrRec** %P.addr
	%.22 = bitcast %System.AnsiStrRec* %.21 to i8*
	tail call void @free(i8* %.22) nounwind
	br label %if3.false
if3.false:
	br label %if2.false
if2.false:
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrAddRef(i8** %S.addr)
{
	%P.addr = alloca %System.AnsiStrRec*, align 8

	%.1 = bitcast i8** %S.addr to i64*
	%.2 = load i64, i64* %.1
	%.3 = sext i8 16 to i64
	%.4 = sub i64 %.2, %.3
	%.5 = inttoptr i64 %.4 to i8*
	%.6 = bitcast i8* %.5 to %System.AnsiStrRec*
	store %System.AnsiStrRec* %.6, %System.AnsiStrRec** %P.addr
	%.7 = load %System.AnsiStrRec*, %System.AnsiStrRec** %P.addr
	%.8 = bitcast i8* null to %System.AnsiStrRec*
	%.9 = icmp ne %System.AnsiStrRec* %.7, %.8
	br i1 %.9, label %if1.true, label %if1.false
if1.true:
	%.10 = load %System.AnsiStrRec*, %System.AnsiStrRec** %P.addr
	%.11 = getelementptr %System.AnsiStrRec, %System.AnsiStrRec* %.10, %SizeInt 0, %SizeInt 4
	%.12 = bitcast i8* %.11 to i32*
	%.13 = load i32, i32* %.12
	%.14 = sext i8 0 to i32
	%.15 = icmp sge i32 %.13, %.14
	br i1 %.15, label %if2.true, label %if2.false
if2.true:
	%.16 = load %System.AnsiStrRec*, %System.AnsiStrRec** %P.addr
	%.17 = getelementptr %System.AnsiStrRec, %System.AnsiStrRec* %.16, %SizeInt 0, %SizeInt 4
	%.18 = bitcast i8* %.17 to i32*
	%.19 = call fastcc i32 @System.InterLockedIncrement(i32* %.18)
	br label %if2.false
if2.false:
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrNew(i8** %S.addr, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System._AStrPtr(i8* %S)
{
	%Result.addr = alloca i8*, align 8

	%S.addr = alloca i8*, align 8
	store i8* %S, i8** %S.addr

	%.1 = load i8*, i8** %S.addr
	%.2 = icmp eq i8* %.1, null
	br i1 %.2, label %if1.true, label %if1.false
if1.true:
	store i8* @System._EmptyStr, i8** %Result.addr
	br label %if1.end
if1.false:
	%.3 = load i8*, i8** %S.addr
	store i8* %.3, i8** %Result.addr
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	%.4 = load i8*, i8** %Result.addr
	ret i8* %.4
}

define fastcc i32 @System._AStrLength(i8* %S)
{
	%Result.addr = alloca i32, align 4

	%S.addr = alloca i8*, align 8
	store i8* %S, i8** %S.addr

	%.1 = load i8*, i8** %S.addr
	%.2 = icmp eq i8* %.1, null
	br i1 %.2, label %if1.true, label %if1.false
if1.true:
	%.3 = sext i8 0 to i32
	store i32 %.3, i32* %Result.addr
	br label %if1.end
if1.false:
	%.4 = bitcast i8** %S.addr to i64**
	%.5 = load i64*, i64** %.4
	%.6 = sub i8 0, 1
	%.7 = getelementptr i64, i64* %.5, i8 %.6
	%.8 = load i64, i64* %.7
	%.9 = trunc i64 %.8 to i32
	store i32 %.9, i32* %Result.addr
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	%.10 = load i32, i32* %Result.addr
	ret i32 %.10
}

define fastcc void @System._AStrAsgCopy(i8** %Dest.addr, i8* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrAsg(i8** %Dest.addr, i8* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrSetLength(i8** %S.addr, i32 %Len)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrCopy(i8** %Dest.addr, i8* %Source, i32 %Start, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrDelete(i8** %Dest.addr, i32 %Index, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrInsert(i8** %Dest.addr, i8* %Source, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromSStr(i8** %Dest.addr, [257 x i8]* %Source.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromWStr(i8** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromUStr(i8** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromACh(i8** %Dest.addr, i8 %ACh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromWCh(i8** %Dest.addr, i16 %WCh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromPACh(i8** %Dest.addr, i8* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromPAChLen(i8** %Dest.addr, i8* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromPWCh(i8** %Dest.addr, i16* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromPWChLen(i8** %Dest.addr, i16* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromAArray(i8** %Dest.addr, i8* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrFromWArray(i8** %Dest.addr, i16* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrCat(i8** %S1.addr, i8* %S2)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrCat3(i8** %S1.addr, i8* %S2, i8* %S3)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._AStrCatN(i8** %S1.addr, i8*** %Source.addr, %SizeInt %Source.high)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrClr(i16** %S.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrNew(i16** %S.addr, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i16* @System._WStrPtr(i16* %S)
{
	%Result.addr = alloca i16*, align 8

	%S.addr = alloca i16*, align 8
	store i16* %S, i16** %S.addr

	%.1 = bitcast i16** %S.addr to i8**
	%.2 = load i8*, i8** %.1
	%.3 = bitcast i8* %.2 to i16*
	store i16* %.3, i16** %Result.addr
	%.4 = load i16*, i16** %Result.addr
	%.5 = bitcast i8* null to i16*
	%.6 = icmp eq i16* %.4, %.5
	br i1 %.6, label %if1.true, label %if1.false
if1.true:
	%.7 = bitcast i16* @System._EmptyWStr to i8*
	%.8 = bitcast i8* %.7 to i16*
	store i16* %.8, i16** %Result.addr
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	%.9 = load i16*, i16** %Result.addr
	ret i16* %.9
}

define fastcc i32 @System._WStrLength(i16* %S)
{
	%Result.addr = alloca i32, align 4

	%S.addr = alloca i16*, align 8
	store i16* %S, i16** %S.addr

	%.1 = bitcast i16** %S.addr to i8**
	%.2 = load i8*, i8** %.1
	%.3 = icmp eq i8* %.2, null
	br i1 %.3, label %if1.true, label %if1.false
if1.true:
	%.4 = sext i8 0 to i32
	store i32 %.4, i32* %Result.addr
	br label %if1.end
if1.false:
	%.5 = bitcast i16** %S.addr to i64**
	%.6 = load i64*, i64** %.5
	%.7 = sub i8 0, 1
	%.8 = getelementptr i64, i64* %.6, i8 %.7
	%.9 = load i64, i64* %.8
	%.10 = trunc i64 %.9 to i32
	store i32 %.10, i32* %Result.addr
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	%.11 = load i32, i32* %Result.addr
	ret i32 %.11
}

define fastcc void @System._WStrAsgCopy(i16** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrAsg(i16** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrSetLength(i16** %S.addr, i32 %Len)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrCopy(i16** %Dest.addr, i16* %Source, i32 %Start, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrDelete(i16** %Dest.addr, i32 %Index, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrInsert(i16** %Dest.addr, i16* %Source, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromSStr(i16** %Dest.addr, [257 x i8]* %Source.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromAStr(i16** %Dest.addr, i8* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromUStr(i16** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromACh(i16** %Dest.addr, i8 %ACh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromWCh(i16** %Dest.addr, i16 %WCh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromPACh(i16** %Dest.addr, i8* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromPAChLen(i16** %Dest.addr, i8* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromPWCh(i16** %Dest.addr, i16* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromPWChLen(i16** %Dest.addr, i16* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromAArray(i16** %Dest.addr, i8* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrFromWArray(i16** %Dest.addr, i16* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrCat(i16** %S1.addr, i16* %S2)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrCat3(i16** %S1.addr, i16* %S2, i16* %S3)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._WStrCatN(i16** %S1.addr, i16*** %Source.addr, %SizeInt %Source.high)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrClr(i16** %S.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrNew(i16** %S.addr, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i16* @System._UStrPtr(i16* %S)
{
	%Result.addr = alloca i16*, align 8

	%S.addr = alloca i16*, align 8
	store i16* %S, i16** %S.addr

	%.1 = bitcast i16** %S.addr to i8**
	%.2 = load i8*, i8** %.1
	%.3 = bitcast i8* %.2 to i16*
	store i16* %.3, i16** %Result.addr
	%.4 = load i16*, i16** %Result.addr
	%.5 = bitcast i8* null to i16*
	%.6 = icmp eq i16* %.4, %.5
	br i1 %.6, label %if1.true, label %if1.false
if1.true:
	%.7 = bitcast i16* @System._EmptyWStr to i8*
	%.8 = bitcast i8* %.7 to i16*
	store i16* %.8, i16** %Result.addr
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	%.9 = load i16*, i16** %Result.addr
	ret i16* %.9
}

define fastcc i32 @System._UStrLength(i16* %S)
{
	%Result.addr = alloca i32, align 4

	%S.addr = alloca i16*, align 8
	store i16* %S, i16** %S.addr

	%.1 = bitcast i16** %S.addr to i8**
	%.2 = load i8*, i8** %.1
	%.3 = icmp eq i8* %.2, null
	br i1 %.3, label %if1.true, label %if1.false
if1.true:
	%.4 = sext i8 0 to i32
	store i32 %.4, i32* %Result.addr
	br label %if1.end
if1.false:
	%.5 = bitcast i16** %S.addr to i64**
	%.6 = load i64*, i64** %.5
	%.7 = sub i8 0, 1
	%.8 = getelementptr i64, i64* %.6, i8 %.7
	%.9 = load i64, i64* %.8
	%.10 = trunc i64 %.9 to i32
	store i32 %.10, i32* %Result.addr
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	%.11 = load i32, i32* %Result.addr
	ret i32 %.11
}

define fastcc void @System._UStrAsgCopy(i16** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrAsg(i16** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrSetLength(i16** %S.addr, i32 %Len)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrCopy(i16** %Dest.addr, i16* %Source, i32 %Start, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrDelete(i16** %Dest.addr, i32 %Index, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrInsert(i16** %Dest.addr, i16* %Source, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromSStr(i16** %Dest.addr, [257 x i8]* %Source.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromWStr(i16** %Dest.addr, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromAStr(i16** %Dest.addr, i8* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromACh(i16** %Dest.addr, i8 %ACh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromWCh(i16** %Dest.addr, i16 %WCh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromPACh(i16** %Dest.addr, i8* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromPAChLen(i16** %Dest.addr, i8* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromPWCh(i16** %Dest.addr, i16* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromPWChLen(i16** %Dest.addr, i16* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromAArray(i16** %Dest.addr, i8* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrFromWArray(i16** %Dest.addr, i16* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrCat(i16** %S1.addr, i16* %S2)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrCat3(i16** %S1.addr, i16* %S2, i16* %S3)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._UStrCatN(i16** %S1.addr, i16*** %Source.addr, %SizeInt %Source.high)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrClr([257 x i8]* %Dest.addr)
{
	%.1 = sext i8 0 to i64
	%.2 = getelementptr [257 x i8], [257 x i8]* %Dest.addr, %SizeInt 0, %SizeInt %.1
	store i8 0, i8* %.2
	br label %.quit
.quit:
	ret void
}

define fastcc i32 @System._StrLength([257 x i8]* %Dest.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i64
	%.2 = getelementptr [257 x i8], [257 x i8]* %Dest.addr, %SizeInt 0, %SizeInt %.1
	%.3 = load i8, i8* %.2
	%.4 = zext i8 %.3 to i32
	store i32 %.4, i32* %Result.addr
	br label %.quit
.quit:
	%.5 = load i32, i32* %Result.addr
	ret i32 %.5
}

define fastcc void @System._SStrAsg([257 x i8]* %Dest.addr, i32 %MaxChars, [257 x i8]* %Source.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrSetLength([257 x i8]* %Dest.addr, i32 %Len)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrCopy([257 x i8]* %Dest.addr, i32 %MaxChars, [257 x i8]* %Source.addr, i32 %Start, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrDelete([257 x i8]* %Dest.addr, i32 %Index, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrInsertS([257 x i8]* %Dest.addr, i32 %MaxChars, [257 x i8]* %Source.addr, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrInsertA([257 x i8]* %Dest.addr, i32 %MaxChars, i8* %Source, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrInsertW([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Source, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrInsertU([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Source, i32 %Index)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromSStr([257 x i8]* %Dest.addr, i32 %MaxChars, [257 x i8]* %Source.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromAStr([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromWStr([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromUStr([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Source)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromACh([257 x i8]* %Dest.addr, i32 %MaxChars, i8 %ACh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromWCh([257 x i8]* %Dest.addr, i32 %MaxChars, i16 %WCh)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromPACh([257 x i8]* %Dest.addr, i32 %MaxChars, i8* %Buf)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromPAChLen([257 x i8]* %Dest.addr, i32 %MaxChars, i8* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromPWCh([257 x i8]* %Dest.addr, i16* %Buf, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromPWChLen([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromAArray([257 x i8]* %Dest.addr, i32 %MaxChars, i8* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrFromWArray([257 x i8]* %Dest.addr, i32 %MaxChars, i16* %Buf, i32 %Count)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrCat([257 x i8]* %S1.addr, i32 %MaxChars, [257 x i8]* %S2.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrCat3([257 x i8]* %S1.addr, i32 %MaxChars, [257 x i8]* %S2.addr, [257 x i8]* %S3.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SStrCatN([257 x i8]* %S1.addr, i32 %MaxChars, [257 x i8]** %Source.addr, %SizeInt %Source.high)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i32 @System._AStrComp(i8* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrComp(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrComp(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrComp([257 x i8]* %S1.addr, [257 x i8]* %S2.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrComp(i8* %S1, i32 %MaxChars1, i8* %S2, i32 %MaxChars2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrComp(i16* %S1, i32 %MaxChars1, i16* %S2, i32 %MaxChars2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompWStr(i8* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompUStr(i8* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompSStr(i8* %S1, [257 x i8]* %S2.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompPa(i8* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompPw(i8* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompAarr(i8* %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompWarr(i8* %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompACh(i8* %S1, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AStrCompWCh(i8* %S1, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompAStr(i16* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompUStr(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompSStr(i16* %S1, [257 x i8]* %S2.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompPa(i16* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompPw(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompAarr(i16* %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompWarr(i16* %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompACh(i16* %S1, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WStrCompWCh(i16* %S1, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompAStr(i16* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompWStr(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompSStr(i16* %S1, [257 x i8]* %S2.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompPa(i16* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompPw(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompAarr(i16* %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompWarr(i16* %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompACh(i16* %S1, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._UStrCompWCh(i16* %S1, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompAStr([257 x i8]* %S1.addr, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompWStr([257 x i8]* %S1.addr, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompUStr([257 x i8]* %S1.addr, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompPa([257 x i8]* %S1.addr, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompPw([257 x i8]* %S1.addr, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompAarr([257 x i8]* %S1.addr, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompWarr([257 x i8]* %S1.addr, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompACh([257 x i8]* %S1.addr, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._SStrCompWCh([257 x i8]* %S1.addr, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompAStr(i8* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompWStr(i8* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompUStr(i8* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompAarr(i8* %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompWarr(i8* %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompACh(i8* %S1, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PaCompWCh(i8* %S1, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompAStr(i16* %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompWStr(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompUStr(i16* %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompAarr(i16* %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompWarr(i16* %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompACh(i16* %S1, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._PwCompWCh(i16* %S1, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompAStr(i8* %S1, i32 %MaxChars, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompWStr(i8* %S1, i32 %MaxChars, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompUStr(i8* %S1, i32 %MaxChars, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompPa(i8* %S1, i32 %MaxChars, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompPw(i8* %S1, i32 %MaxChars, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompWarr(i8* %S1, i32 %MaxChars1, i16* %S2, i32 %MaxChars2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompACh(i8* %S1, i32 %MaxChars, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AarrCompWCh(i8* %S1, i32 %MaxChars, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompAStr(i16* %S1, i32 %MaxChars, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompWStr(i16* %S1, i32 %MaxChars, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompUStr(i16* %S1, i32 %MaxChars, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompPa(i16* %S1, i32 %MaxChars, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompPw(i16* %S1, i32 %MaxChars, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompAarr(i16* %S1, i32 %MaxChars1, i8* %S2, i32 %MaxChars2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompACh(i16* %S1, i32 %MaxChars, i8 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WarrCompWCh(i16* %S1, i32 %MaxChars, i16 %Ch)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompAStr(i8 %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompUStr(i8 %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompSStr(i8 %S1, [257 x i8]* %S2.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompPa(i8 %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompPw(i8 %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompAarr(i8 %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._AChCompWarr(i8 %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompAStr(i16 %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompUStr(i16 %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompSStr(i16 %S1, [257 x i8]* %S2.addr)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompPa(i16 %S1, i8* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompPw(i16 %S1, i16* %S2)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompAarr(i16 %S1, i8* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc i32 @System._WChCompWarr(i16 %S1, i16* %S2, i32 %MaxChars)
{
	%Result.addr = alloca i32, align 4

	%.1 = sext i8 0 to i32
	store i32 %.1, i32* %Result.addr
	br label %.quit
.quit:
	%.2 = load i32, i32* %Result.addr
	ret i32 %.2
}

define fastcc void @System._VarClr(%System.TVarData* %V.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._VarOp(%System.TVarData* %V1.addr, %System.TVarData* %V2.addr, i32 %Op)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._VarNot(%System.TVarData* %V.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._VarNeg(%System.TVarData* %V.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._VarCopy(%System.TVarData* %Dest.addr, %System.TVarData* %Source.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Var2AStr(%System.TVarData* %V.addr, i8** %Dest.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Var2WStr(%System.TVarData* %V.addr, i16** %Dest.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Var2UStr(%System.TVarData* %V.addr, i16** %Dest.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Var2SStr(%System.TVarData* %V.addr, [257 x i8]* %Dest.addr, i32 %MaxChars)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._Var2Intf(%System.TVarData* %V.addr, i8*** %Dest.addr)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._IntfCast(i8*** %Dest.addr, i8** %Source, %System.TGUID* %IID.addr)
{
	%Source.addr = alloca i8**, align 8
	store i8** %Source, i8*** %Source.addr

	%.1 = load i8**, i8*** %Source.addr
	%.2 = bitcast i8* null to i8**
	%.3 = icmp eq i8** %.1, %.2
	br i1 %.3, label %if1.true, label %if1.false
if1.true:
	%.4 = call fastcc i8* @System._IntfClr(i8*** %Dest.addr)
	br label %if1.end
if1.false:
	%.5 = load i8**, i8*** %Source.addr
	%.6 = bitcast i8** %.5 to i8***
	%.7 = load i8**, i8*** %.6
	%.8 = getelementptr i8*, i8** %.7, %SizeInt 0
	%.9 = load i8*, i8** %.8
	%.10 = bitcast i8* %.9 to i32 (i8*, %System.TGUID*, i8*)*
	%.11 = bitcast i8** %.5 to i8*
	%.12 = bitcast i8*** %Dest.addr to i8*
	%.13 = call cc 64 i32 %.10(i8* %.11, %System.TGUID* %IID.addr, i8* %.12)
	%.14 = sext i8 0 to i32
	%.15 = icmp ne i32 %.13, %.14
	br i1 %.15, label %if2.true, label %if2.false
if2.true:
	call fastcc void @System.Error(i8 23)
	br label %if2.false
if2.false:
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	ret void
}

define fastcc i8* @System._IntfClr(i8*** %Dest.addr)
{
	%Result.addr = alloca i8*, align 8

	%P.addr = alloca i8*, align 8

	%.1 = bitcast i8*** %Dest.addr to i8*
	store i8* %.1, i8** %Result.addr
	%.2 = load i8**, i8*** %Dest.addr
	%.3 = bitcast i8* null to i8**
	%.4 = icmp ne i8** %.2, %.3
	br i1 %.4, label %if1.true, label %if1.false
if1.true:
	%.5 = bitcast i8*** %Dest.addr to i8**
	%.6 = load i8*, i8** %.5
	store i8* %.6, i8** %P.addr
	%.7 = bitcast i8*** %Dest.addr to i8**
	store i8* null, i8** %.7
	%.8 = bitcast i8** %P.addr to i8***
	%.9 = load i8**, i8*** %.8
	%.10 = bitcast i8** %.9 to i8***
	%.11 = load i8**, i8*** %.10
	%.12 = getelementptr i8*, i8** %.11, %SizeInt 2
	%.13 = load i8*, i8** %.12
	%.14 = bitcast i8* %.13 to i32 (i8*)*
	%.15 = bitcast i8** %.9 to i8*
	%.16 = call cc 64 i32 %.14(i8* %.15)
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	%.17 = load i8*, i8** %Result.addr
	ret i8* %.17
}

define fastcc void @System._IntfCopy(i8*** %Dest.addr, i8** %Source)
{
	%Source.addr = alloca i8**, align 8
	store i8** %Source, i8*** %Source.addr

	%P.addr = alloca i8*, align 8

	%.1 = bitcast i8*** %Dest.addr to i8**
	%.2 = load i8*, i8** %.1
	store i8* %.2, i8** %P.addr
	%.3 = load i8**, i8*** %Source.addr
	%.4 = bitcast i8* null to i8**
	%.5 = icmp ne i8** %.3, %.4
	br i1 %.5, label %if1.true, label %if1.false
if1.true:
	%.6 = load i8**, i8*** %Source.addr
	%.7 = bitcast i8** %.6 to i8***
	%.8 = load i8**, i8*** %.7
	%.9 = getelementptr i8*, i8** %.8, %SizeInt 1
	%.10 = load i8*, i8** %.9
	%.11 = bitcast i8* %.10 to i32 (i8*)*
	%.12 = bitcast i8** %.6 to i8*
	%.13 = call cc 64 i32 %.11(i8* %.12)
	br label %if1.false
if1.false:
	%.14 = bitcast i8*** %Dest.addr to i8**
	%.15 = bitcast i8*** %Source.addr to i8**
	%.16 = load i8*, i8** %.15
	store i8* %.16, i8** %.14
	%.17 = load i8*, i8** %P.addr
	%.18 = icmp ne i8* %.17, null
	br i1 %.18, label %if2.true, label %if2.false
if2.true:
	%.19 = bitcast i8** %P.addr to i8***
	%.20 = load i8**, i8*** %.19
	%.21 = bitcast i8** %.20 to i8***
	%.22 = load i8**, i8*** %.21
	%.23 = getelementptr i8*, i8** %.22, %SizeInt 2
	%.24 = load i8*, i8** %.23
	%.25 = bitcast i8* %.24 to i32 (i8*)*
	%.26 = bitcast i8** %.20 to i8*
	%.27 = call cc 64 i32 %.25(i8* %.26)
	br label %if2.false
if2.false:
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._IntfAddRef(i8** %Dest)
{
	%Dest.addr = alloca i8**, align 8
	store i8** %Dest, i8*** %Dest.addr

	%.1 = load i8**, i8*** %Dest.addr
	%.2 = bitcast i8* null to i8**
	%.3 = icmp ne i8** %.1, %.2
	br i1 %.3, label %if1.true, label %if1.false
if1.true:
	%.4 = load i8**, i8*** %Dest.addr
	%.5 = bitcast i8** %.4 to i8***
	%.6 = load i8**, i8*** %.5
	%.7 = getelementptr i8*, i8** %.6, %SizeInt 1
	%.8 = load i8*, i8** %.7
	%.9 = bitcast i8* %.8 to i32 (i8*)*
	%.10 = bitcast i8** %.4 to i8*
	%.11 = call cc 64 i32 %.9(i8* %.10)
	br label %if1.false
if1.false:
	br label %.quit
.quit:
	ret void
}

define fastcc i8 @System._SetIn(i8* %S.addr, i8 %Size, i8 %Elem)
{
	%Result.addr = alloca i8, align 1

	store i8 0, i8* %Result.addr
	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc void @System._SetElem(i8* %S.addr, i8 %Size, i8 %Elem)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetRange(i8* %S.addr, i8 %Size, i8 %Lo, i8 %Hi)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetUnion(i8* %Dest.addr, i8* %Src.addr, i8 %Size)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetSub(i8* %Dest.addr, i8* %Src.addr, i8 %Size)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetInterset(i8* %Dest.addr, i8* %Src.addr, i8 %Size)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i8 @System._SetNE(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	store i8 0, i8* %Result.addr
	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc i8 @System._SetEQ(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	store i8 0, i8* %Result.addr
	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc i8 @System._SetLE(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	store i8 0, i8* %Result.addr
	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc i8 @System._SetGE(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	store i8 0, i8* %Result.addr
	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc void @System._SetInclude(i8* %S.addr, i8 %Size, i8 %Elem)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetExclude(i8* %S.addr, i8 %Size, i8 %Elem)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i8 @System._NSetIn(i8* %S.addr, i8 %Size, i8 %Elem)
{
	%Result.addr = alloca i8, align 1

	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc void @System._NSetElem(i8* %S.addr, i8 %Size, i8 %Elem)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._NSetRange(i8* %S.addr, i8 %Size, i8 %Lo, i8 %Hi)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._NSetUnion(i8* %Dest.addr, i8* %Src.addr, i8 %Size)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._NSetSub(i8* %Dest.addr, i8* %Src.addr, i8 %Size)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._NSetInterset(i8* %Dest.addr, i8* %Src.addr, i8 %Size)
{
	br label %.quit
.quit:
	ret void
}

define fastcc i8 @System._NSetNE(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc i8 @System._NSetEQ(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc i8 @System._NSetLE(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc i8 @System._NSetGE(i8* %Left.addr, i8* %Right.addr, i8 %Size)
{
	%Result.addr = alloca i8, align 1

	br label %.quit
.quit:
	%.1 = load i8, i8* %Result.addr
	ret i8 %.1
}

define fastcc void @System._NSetInclude(i8* %S.addr, i8 %Size, i8 %Elem)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._NSetExclude(i8* %S.addr, i8 %Size, i8 %Elem)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetCopy(i8* %Dest.addr, i8* %Src.addr, i8 %d_lo, i8 %d_hi, i8 %s_lo, i8 %s_hi)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetInflate(i8* %Dest.addr, i8* %Src.addr, i8 %lo, i8 %hi, i8 %maxHi)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System._SetExpand(i8* %Dest.addr, i8* %Src.addr, i8 %lo, i8 %hi)
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.Error(i8 %errorCode)
{
	%errorCode.addr = alloca i8, align 1
	store i8 %errorCode, i8* %errorCode.addr

	%.1 = load void (i8, i8*)*, void (i8, i8*)** @System.ErrorProc
	%.2 = bitcast i8* null to void (i8, i8*)*
	%.3 = icmp eq void (i8, i8*)* %.1, %.2
	br i1 %.3, label %if1.true, label %if1.false
if1.true:
	%.4 = load void (i8, i8*)*, void (i8, i8*)** @System.ErrorProc
	%.5 = load i8, i8* %errorCode.addr
	call fastcc void %.4(i8 %.5, i8* null)
	br label %if1.false
if1.false:
	%.6 = sext i8 1 to i32
	call fastcc void @System.Halt(i32 %.6)
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.Halt(i32 %code)
{
	%code.addr = alloca i32, align 4
	store i32 %code, i32* %code.addr

	%.1 = load i32, i32* %code.addr
	call fastcc void @System._CrtExit(i32 %.1)
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.FreeAndNil(i8** %obj.addr)
{
	%temp.addr = alloca i8*, align 8

	%.1 = load i8*, i8** %obj.addr
	store i8* %.1, i8** %temp.addr
	store i8* null, i8** %obj.addr
	%.2 = load i8*, i8** %temp.addr
	call fastcc void @System.TObject.Free(i8* %.2)
	br label %.quit
.quit:
	ret void
}

define internal fastcc i8* @System._FinalizeRecord(i8* %P, i8* %TypeInfo)
{
	%Result.addr = alloca i8*, align 8

	store i8* null, i8** %Result.addr
	br label %.quit
.quit:
	%.1 = load i8*, i8** %Result.addr
	ret i8* %.1
}

define internal fastcc void @System.InvokeImplGetter(i8* %Self, i32 %ImplGetter, i8*** %Result.addr)
{
	%Self.addr = alloca i8*, align 8
	store i8* %Self, i8** %Self.addr

	%ImplGetter.addr = alloca i32, align 4
	store i32 %ImplGetter, i32* %ImplGetter.addr

	%M.addr = alloca [2 x i8*], align 16

	%.1 = bitcast [2 x i8*]* %M.addr to %System.TMethod*
	%.2 = getelementptr %System.TMethod, %System.TMethod* %.1, %SizeInt 0, %SizeInt 8
	%.3 = bitcast i8* %.2 to i8**
	%.4 = load i8*, i8** %Self.addr
	store i8* %.4, i8** %.3
	br label %expr10.1
expr10.1:
	%.5 = load i32, i32* %ImplGetter.addr
	%.6 = icmp uge i32 %.5, 4278190080
	br i1 %.6, label %expr10.2, label %expr10.3
expr10.2:
	%.7 = load i32, i32* %ImplGetter.addr
	%.8 = icmp ule i32 %.7, 4294967295
	br label %expr10.3
expr10.3:
	%.9 = phi i1 [ %.6, %expr10.1], [ %.8, %expr10.2 ]
	br i1 %.9, label %if1.true, label %if1.false
if1.true:
	%.10 = load i8*, i8** %Self.addr
	%.11 = ptrtoint i8* %.10 to i32
	%.12 = load i32, i32* %ImplGetter.addr
	%.13 = and i32 %.12, 16777215
	%.14 = add i32 %.11, %.13
	%.15 = inttoptr i32 %.14 to i8*
	%.16 = bitcast i8* %.15 to i8**
	call fastcc void @System._IntfCopy(i8*** %Result.addr, i8** %.16)
	br label %if1.end
if1.false:
	br label %expr11.4
expr11.4:
	%.17 = load i32, i32* %ImplGetter.addr
	%.18 = icmp uge i32 %.17, 4261412864
	br i1 %.18, label %expr11.5, label %expr11.6
expr11.5:
	%.19 = load i32, i32* %ImplGetter.addr
	%.20 = icmp ule i32 %.19, 4278190079
	br label %expr11.6
expr11.6:
	%.21 = phi i1 [ %.18, %expr11.4], [ %.20, %expr11.5 ]
	br i1 %.21, label %if2.true, label %if2.false
if2.true:
	%.22 = bitcast [2 x i8*]* %M.addr to %System.TMethod*
	%.23 = getelementptr %System.TMethod, %System.TMethod* %.22, %SizeInt 0, %SizeInt 0
	%.24 = bitcast i8* %.23 to i8**
	%.25 = bitcast i8** %Self.addr to i64*
	%.26 = load i32, i32* %ImplGetter.addr
	%.27 = trunc i32 %.26 to i16
	%.28 = load i64, i64* %.25
	%.29 = sext i16 %.27 to i64
	%.30 = add i64 %.28, %.29
	%.31 = inttoptr i64 %.30 to i8**
	%.32 = load i8*, i8** %.31
	store i8* %.32, i8** %.24
	%.33 = getelementptr [2 x i8*], [2 x i8*]* %M.addr, i32 0, i32 1
	%.34 = load i8*, i8** %.33
	%.35 = getelementptr [2 x i8*], [2 x i8*]* %M.addr, i32 0, i32 0
	%.36 = load i8*, i8** %.35
	%.37 = bitcast i8* %.36 to void (i8*, i8***)*
	call fastcc void %.37(i8* %.34, i8*** %Result.addr)
	br label %if2.end
if2.false:
	%.38 = bitcast [2 x i8*]* %M.addr to %System.TMethod*
	%.39 = getelementptr %System.TMethod, %System.TMethod* %.38, %SizeInt 0, %SizeInt 0
	%.40 = bitcast i8* %.39 to i8**
	%.41 = load i32, i32* %ImplGetter.addr
	%.42 = inttoptr i32 %.41 to i8*
	store i8* %.42, i8** %.40
	%.43 = getelementptr [2 x i8*], [2 x i8*]* %M.addr, i32 0, i32 1
	%.44 = load i8*, i8** %.43
	%.45 = getelementptr [2 x i8*], [2 x i8*]* %M.addr, i32 0, i32 0
	%.46 = load i8*, i8** %.45
	%.47 = bitcast i8* %.46 to void (i8*, i8***)*
	call fastcc void %.47(i8* %.44, i8*** %Result.addr)
	br label %if2.end
if2.end:
	br label %if1.end
if1.end:
	br label %.quit
.quit:
	ret void
}

define internal fastcc i8* @System.GetDynaMethod(i8* %vmt, i16 %selector)
{
	%Result.addr = alloca i8*, align 8

	%vmt.addr = alloca i8*, align 8
	store i8* %vmt, i8** %vmt.addr

	%selector.addr = alloca i16, align 2
	store i16 %selector, i16* %selector.addr

	%dynaTab.addr = alloca %System.GetDynaMethod.TDynaMethodTable*, align 8

	%Parent.addr = alloca i8*, align 8

	%Addrs.addr = alloca i8**, align 8

	%I.addr = alloca i32, align 4

	%.V1.addr = alloca i32, align 4

	br label %while1.begin
while1.begin:
	%.1 = icmp ne i8 0, 1
	br i1 %.1, label %while1.body, label %while1.end
while1.body:
	%.2 = load i8*, i8** %vmt.addr
	%.3 = getelementptr i8, i8* %.2, i32 -48
	%.4 = bitcast i8* %.3 to i8**
	%.5 = load i8*, i8** %.4
	%.6 = bitcast i8* %.5 to %System.GetDynaMethod.TDynaMethodTable*
	store %System.GetDynaMethod.TDynaMethodTable* %.6, %System.GetDynaMethod.TDynaMethodTable** %dynaTab.addr
	%.7 = load %System.GetDynaMethod.TDynaMethodTable*, %System.GetDynaMethod.TDynaMethodTable** %dynaTab.addr
	%.8 = bitcast i8* null to %System.GetDynaMethod.TDynaMethodTable*
	%.9 = icmp ne %System.GetDynaMethod.TDynaMethodTable* %.7, %.8
	br i1 %.9, label %if2.true, label %if2.false
if2.true:
	%.10 = sext i8 0 to i32
	store i32 %.10, i32* %I.addr
	%.11 = load %System.GetDynaMethod.TDynaMethodTable*, %System.GetDynaMethod.TDynaMethodTable** %dynaTab.addr
	%.12 = getelementptr %System.GetDynaMethod.TDynaMethodTable, %System.GetDynaMethod.TDynaMethodTable* %.11, %SizeInt 0, %SizeInt 0
	%.13 = bitcast i8* %.12 to i16*
	%.14 = load i16, i16* %.13
	%.15 = zext i16 %.14 to i32
	%.16 = sext i8 1 to i32
	%.17 = sub i32 %.15, %.16
	store i32 %.17, i32* %.V1.addr
	br label %for3.begin
for3.begin:
	%.18 = load i32, i32* %I.addr
	%.19 = load i32, i32* %.V1.addr
	%.20 = icmp sle i32 %.18, %.19
	br i1 %.20, label %forloop1, label %for3.br
forloop1:
	%.21 = load i32, i32* %I.addr
	%.22 = sext i32 %.21 to i64
	%.23 = load %System.GetDynaMethod.TDynaMethodTable*, %System.GetDynaMethod.TDynaMethodTable** %dynaTab.addr
	%.24 = getelementptr %System.GetDynaMethod.TDynaMethodTable, %System.GetDynaMethod.TDynaMethodTable* %.23, %SizeInt 0, %SizeInt 2
	%.25 = bitcast i8* %.24 to [10000000 x i16]*
	%.26 = getelementptr [10000000 x i16], [10000000 x i16]* %.25, %SizeInt 0, %SizeInt %.22
	%.27 = load i16, i16* %.26
	%.28 = load i16, i16* %selector.addr
	%.29 = sext i16 %.27 to i32
	%.30 = sext i16 %.28 to i32
	%.31 = icmp eq i32 %.29, %.30
	br i1 %.31, label %if4.true, label %if4.false
if4.true:
	%.32 = load %System.GetDynaMethod.TDynaMethodTable*, %System.GetDynaMethod.TDynaMethodTable** %dynaTab.addr
	%.33 = getelementptr %System.GetDynaMethod.TDynaMethodTable, %System.GetDynaMethod.TDynaMethodTable* %.32, %SizeInt 0, %SizeInt 2
	%.34 = bitcast i8* %.33 to [10000000 x i16]*
	%.35 = bitcast [10000000 x i16]* %.34 to i8*
	%.36 = load %System.GetDynaMethod.TDynaMethodTable*, %System.GetDynaMethod.TDynaMethodTable** %dynaTab.addr
	%.37 = getelementptr %System.GetDynaMethod.TDynaMethodTable, %System.GetDynaMethod.TDynaMethodTable* %.36, %SizeInt 0, %SizeInt 0
	%.38 = bitcast i8* %.37 to i16*
	%.39 = load i16, i16* %.38
	%.40 = zext i16 %.39 to i32
	%.41 = sext i8 2 to i32
	%.42 = mul i32 %.40, %.41
	%.43 = getelementptr i8, i8* %.35, i32 %.42
	%.44 = bitcast i8* %.43 to i8**
	store i8** %.44, i8*** %Addrs.addr
	%.45 = bitcast i8*** %Addrs.addr to i8**
	%.46 = load i32, i32* %I.addr
	%.47 = sext i8 8 to i32
	%.48 = mul i32 %.46, %.47
	%.49 = load i8*, i8** %.45
	%.50 = getelementptr i8, i8* %.49, i32 %.48
	%.51 = bitcast i8* %.50 to i8**
	%.52 = load i8*, i8** %.51
	store i8* %.52, i8** %Result.addr
	br label %.quit
if4.false:
	br label %for3.cont
for3.cont:
	%.53 = load i32, i32* %I.addr
	%.54 = add i32 %.53, 1
	store i32 %.54, i32* %I.addr
	br label %for3.begin
for3.br:
	br label %if2.false
if2.false:
	%.55 = load i8*, i8** %vmt.addr
	%.56 = getelementptr i8, i8* %.55, i32 -36
	%.57 = bitcast i8* %.56 to i8**
	%.58 = load i8*, i8** %.57
	store i8* %.58, i8** %Parent.addr
	%.59 = load i8*, i8** %Parent.addr
	%.60 = icmp eq i8* %.59, null
	br i1 %.60, label %if5.true, label %if5.false
if5.true:
	br label %while1.end
if5.false:
	%.61 = bitcast i8** %Parent.addr to i8***
	%.62 = load i8**, i8*** %.61
	%.63 = load i8*, i8** %.62
	store i8* %.63, i8** %vmt.addr
	br label %while1.end
while1.end:
	store i8* null, i8** %Result.addr
	br label %.quit
.quit:
	%.64 = load i8*, i8** %Result.addr
	ret i8* %.64
}

define fastcc void @System.$init()
{
	br label %.quit
.quit:
	ret void
}

define fastcc void @System.$final()
{
	br label %.quit
.quit:
	ret void
}

