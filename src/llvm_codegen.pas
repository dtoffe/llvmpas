unit llvm_codegen;

{$mode Delphi}{$H+}{$J-}
{$define CHECKTYPE}
{$ASSERTIONS ON}

interface

uses SysUtils, Classes, ast, cntx, llvm_codepack, inst, hashtable;

type
  TExprState = (esNone, esAddrOfMember);
  TCGState = (gsInTop, gsInFunc);
  TCGStates = set of TCGState;
  TLLVMIntrinsic = (llvm_memcpy, llvm_memmove, llvm_rint, llvm_ovfi8, llvm_ovfi16, llvm_ovfi32,
    llvm_ovfi64, llvm_malloc, llvm_free);
  TLLVMIntrinsics = set of TLLVMIntrinsic;
  TSysRoutine = (sys_ovf_check, sys_range_check, sys_io_check, sys_astr, sys_wstr, sys_ustr,
    sys_sstr, sys_var, sys_conv, sys_math, sys_raise);
  TSysRoutines = set of TSysRoutine;
  TBaseType = (btErr, btInt, btFlt, btCur, btBol, btChr, btStr, btSet, btVar, btPtr);
  TLLVMType = (ltI1, ltI8, ltI16, ltI32, ltI64, ltF32, ltF64, ltStruct, ltPtr);
  TVarState = (vasAddrOfVar, vasCurrConst, vasAddrValue);
  TVarStates = set of TVarState;
  PVarInfo = ^TVarInfo;

  TVarInfo = record
    Name, TyStr: string;
    States: TVarStates;
    Align: string;
  end;

  TWStrInitInfo = class
  public
    VarName: string;
    DataVarName: string;
    DataTyStr: string;
  end;

  TCPUKind = (ckX86, ckX86_64, ckARM, ckXCore, ckPPC32, ckPPC64);
  TCPUWordSize = (cws32, cws64);
  TAddSubMulOp = opcADD..opcMUL;
  TLLVMIntType = ltI8..ltI64;
  ECodeGenError = class(Exception);

  TEmitFuncContext = class
  public
    Func: TFunction;
    ResultVar, SelfVar: TVariable;
    MangledName: string;
    FrameDecl: string;
    FrameTyStr: string;
    FrameAlign: byte;
    Level: byte;
    LinkedFrameIndex: word;
    HasAutoFreeVar: boolean;
    NeedFrame: boolean;
    HasNest: boolean;
    RetConverted: boolean;
    IsSafecall: boolean;
    IsMeth, IsCtor, IsDtor: boolean;
    IsStaticFunc, IsClassFunc: boolean;
    UnreachableUsed, TerminatedUsed: boolean;
    TempID, LabelID, PadID: integer;
    Codes: TStringList;
    Landingpads, LandingpadStack: TStringList;
    constructor Create;
    destructor Destroy; override;
  end;

  TCodeGen = class
  private
    FContext: TCompileContext;
    FModule: TModule;
    FCodes: TStringList;
    FDecls: TStringList;
    FExtDecls: TStringList;
    FExternalSymbols: TPtrHashTable;
    FEmittedSymbols: TPtrHashTable;
    FStrConstList, FSetConstList: THashTable;
    FWStrInitList: TFPList;
    FTopCntx, FCurCntx: TEmitFuncContext;
    FCntxList: TFPList;
    FIntrinsics: TLLVMIntrinsics;
    FCurLabel: string;
    FExprID: integer;
    FNewInstanceFunc, FAfterConstructionFunc, FFreeInstanceFunc, FBeforeDestructionFunc: TMethod;
    function WriteCode(const S: string): integer; overload;
    function WriteCode(const S: string; const Args: array of const): integer; overload;
    function WriteCodeNI(const s: string): integer;
    function WriteLabel(const S: string): integer;
    procedure WriteDecl(const S: string); overload;
    procedure WriteDecl(const S: string; const Args: array of const); overload;
    procedure EmitError(const Msg: string); overload;
    procedure EmitError(const Msg: string; const Args: array of const); overload;
    procedure EmitError(const Coord: TAstNodeCoord; const Msg: string); overload;
    procedure EmitError(const Coord: TAstNodeCoord; const Msg: string; const Args: array of const); overload;
    function TempVar: string;
    function LabelStr(const Prefix: string = 'L.'): string;
    function CurLandingPad: string;
    procedure EnterLandingpad(const LPad: string); overload;
    procedure EnterLandingpad(Handler: TCmd); overload;
    procedure LeaveLandingpad;
    function TypeStr(Typ: TType): string;
    function ProcTypeStr(T: TProceduralType; const Name: string = ''): string;
    function ArgTypeStr(T: TType; Modifier: TArgumentModifier): string;
    function ArgDeclStr(Arg: TFuncParam; NeedName: boolean): string;
    function CCStr(cc: TCallingConvention): string;
    function FuncDecl(F: TFunctionDecl; NeedArgName: boolean; const Name: string = ''): string;
    procedure EmitSymbolDecl(Sym: TSymbol);
    procedure EmitTypeDecl(T: TType);
    procedure EmitGlobalVarDecl(V: TVariable);
    procedure EmitGlobalConstDecl(C: TConstant);
    procedure EmitStrA(pub: boolean; const Name, s: string; emitTy: boolean = False);
    procedure EmitStrW(pub: boolean; const Name: string; const s: WideString; emitTy: boolean = False);
    procedure EmitStrU(pub: boolean; const Name: string; const s: WideString; emitTy: boolean = False);
    procedure EmitStrPa(pub: boolean; const Name, s: string; emitTy: boolean = False);
    procedure EmitStrPw(pub: boolean; const Name: string; const s: WideString; emitTy: boolean = False);
    procedure AddInitWStr(const VarName, DataVarName, DataTyStr: string);
    procedure ClearWStrInitList;
    procedure AddExternalSymbol(Sym: TSymbol);
    procedure AddSystemRoutine(Routine: TSystemRoutine);
{$IFNDEF DEBUG}
      inline;
{$ENDIF}
    procedure EmitExternalDecl;
    procedure EmitSysTypeInfo;
    procedure EmitCallSys(Routine: TSystemRoutine; const Typs, Args: array of string; const RetVar: string = '');
    procedure EmitCall(Func: TFunctionDecl; const Typs, Args: array of string; const RetVar: string); overload;
    procedure EmitCast(var R: TVarInfo; RT, LT: TType; const debugStr: string = '');
    procedure EmitRangeCheck(var V: TVarInfo; RT, LT: TType);
    function IsRangeCheckNeeded(RT, LT: TType): boolean;
    procedure EmitFuncCall(Left, Right: TBaseOp; Fun: TFunctionDecl; FunT: TProceduralType; var Result: TVarInfo);
    procedure EmitBuiltin(E: TBinaryOp; Func: TBuiltinFunction; Args: TListOp; var Result: TVarInfo);
    procedure EmitRtti_Class(T: TClassType);
    procedure EmitRtti_Record(T: TRecordType);
    procedure EmitRtti_Object(T: TObjectType);
    procedure EmitRtti_Intf(T: TInterfaceType);
    procedure EmitRtti_Class_External(T: TClassType);
    procedure EmitRtti_Record_External(T: TRecordType);
    procedure EmitRtti_Object_External(T: TObjectType);
    procedure EmitRtti_Intf_External(T: TInterfaceType);
    procedure EmitOp(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_LoadRef(Ref: TSymbol; var Result: TVarInfo);
    procedure EmitOp_Load(E: TSymbolOp; var Result: TVarInfo);
    procedure EmitOp_LoadConst(E: TConstOp; var Result: TVarInfo);
    procedure EmitOp_LoadConstValue(const Value: TValueRec; T: TType; var Result: TVarInfo);
    procedure EmitOp_LoadSelf(var Result: TVarInfo);
    procedure EmitOp_LoadObj(E: TBaseOp; var Ret: TVarInfo);
    procedure EmitOp_Addr(E: TUnaryOp; var Result: TVarInfo);
    procedure EmitOp_ProcAddr(E: TUnaryOp; var ResultVar: TVarInfo);
    procedure EmitOp_Inst(E: TUnaryOp; var Result: TVarInfo);
    procedure EmitOp_Not(E: TUnaryOp; var Result: TVarInfo);
    procedure EmitOp_Neg(E: TUnaryOp; var Result: TVarInfo);
    procedure EmitOp_Cast(E: TBinaryOp; var Result: TVarInfo);
    procedure EmitOp_Index(E: TBinaryOp; var Result: TVarInfo);
    procedure EmitOp_Member(E: TBinaryOp; var Result: TVarInfo);
    procedure EmitOp_Call(E: TBinaryOp; var Result: TVarInfo);
    procedure EmitOp_VarLoad(var Result: TVarInfo); overload;
    procedure EmitOp_VarLoad(const Src: TVarInfo; out Des: TVarInfo); overload;
    procedure EmitOp_Ptr(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_Int(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_Int64(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_Float(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_Currency(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_Char(E: TBaseOp; var Result: TVarInfo);
    procedure EmitOp_IntOvf(var L, R, Result: TVarInfo; Op: TAddSubMulOp; Ty: TLLVMIntType; IsSign: boolean);
    procedure EmitOp_Boolean(E: TBaseOp; var Result: TVarInfo);
    procedure EmitIns_Bitcast(var Result: TVarInfo; const desT: string);
    procedure EmitIns_IntTrunc(var Result: TVarInfo; const desT: string);
    procedure EmitIns_FltTrunc(var Result: TVarInfo; const desT: string);
    procedure EmitIns_IntExt(var Result: TVarInfo; const desT: string; sign: boolean; const debugStr: string = '');
    procedure EmitIns_FltExt(var Result: TVarInfo; const desT: string);
    procedure EmitIns_Int2Flt(var Result: TVarInfo; const desT: string; sign: boolean);
    procedure EmitIns_Int2Cur(var Result: TVarInfo; sign: boolean);
    procedure EmitIns_Int2Bol(var Result: TVarInfo);
    procedure EmitIns_Bol2Bol(var Result: TVarInfo; typ: TType);
    procedure EmitIns_Bol2I1(var Result: TVarInfo);
    procedure EmitIns_Bit2Bol(var Result: TVarInfo);
    procedure EmitIns_Flt2Cur(var Result: TVarInfo);
    procedure EmitIns_Cur2Flt(var Result: TVarInfo; const desT: string);
    procedure EmitIns_Cur2Comp(var Result: TVarInfo);
    procedure EmitIns_Ptr2Int(var Result: TVarInfo; const desT: string);
    procedure EmitIns_Int2Ptr(var Result: TVarInfo; const desT: string);
    procedure EmitIns_Memcpy(const desT, desN, srcT, srcN: string; len: int64; vol: boolean = False);
    procedure EmitLoadVmt(const VmtVar, VmtTy: string; IsInst: boolean; Offset: integer; out FunPtr: string);
    procedure EmitLoadVmtCast(const VmtVar, VmtTy: string; IsInst: boolean; CastFunc: TMethod;
      out FunPtr, FunTy: string);
    procedure EmitExternals;
    procedure EmitIntrinsics;
    procedure EmitCmd(Cmd: TCmd; Pre: TCmd);
    procedure EmitCmds(List: TFPList);
{$IFNDEF DEBUG}
      inline;
{$ENDIF}
    procedure EmitCmdOfOp(E: TBaseOp);
    procedure EmitVarUninit(Func: TFunction);
  public
    CPU: TCPUKind;
    CPUWordSize: TCPUWordSize;
    DumpLineNo: boolean;
    DumpDebugInfo: boolean;
    DefCC: string;
    NativeIntStr, LongDoubleStr: string;
    LLVMTarget: string;
    constructor Create(ACntx: TCompileContext);
    destructor Destroy; override;
    procedure EmitModuleDecl(M: TModule);
    procedure Emit(Func: TFunction);
    procedure EmitFunc(Func: TFunctionDecl);
    function GetIR: string;
  end;

implementation

const
  StructTypes = [typString, typVariant, typUntype, typRecord, typObject, typArray, typSet, typOpenArray];
  Visibility: array[boolean] of string = ('private', '');
  TlsStr: array[boolean] of string = ('', 'thread_local(initialexec)');
  llvmTypeNames: array[ltI1..ltF64] of string = ('i1', 'i8', 'i16', 'i32', 'i64', 'float', 'double');

const
  typIntMaps: array[TIntKind] of string = ('i8', 'i8', 'i16', 'i16', 'i32', 'i32', 'i64', 'i64');
  typBoolMaps: array[TBoolKind] of string = ('i8', 'i8', 'i16', 'i32');
  typCharMaps: array [TCharKind] of string = ('i8', 'i16');
  typNumericMaps: array[TNumericKind] of string = ('float', 'double', 'double', 'i64', 'i64', 'i64');
  typMaps: array[typUntype..typDynamicArray] of string =
    ('i8', 'i32', 'double', 'i8', 'i8', 'i8*', 'i8*', 'i16*', 'i8*', '%System.TVarData', 'i8*',
    'i8*', 'i8*', 'i8*', 'i8*', 'i8*', 'i8**', 'i8*', 'i8', 'i8', 'i8', 'i8*', 'i8*');

type
  TBaseKind = (bkErr, bkBol, bkInt, bkBig, bkFlt, bkCur, bkChr, bkStr, bkVar, bkPtr, bkAny);

const
  SimpleOpMaps: array[bkBol..bkAny, bkBol..bkAny] of TBaseKind =
    ((bkBol, bkErr, bkErr, bkErr, bkErr, bkErr, bkErr, bkVar, bkErr, bkAny), (bkErr, bkInt, bkBig,
    bkFlt, bkCur, bkErr, bkErr,
    bkVar, bkPtr, bkAny), (bkErr, bkBig, bkBig, bkFlt, bkCur, bkErr, bkErr, bkVar, bkPtr, bkAny),
    (bkErr, bkFlt, bkFlt, bkFlt, bkCur, bkErr, bkErr, bkVar, bkErr, bkAny), (bkErr, bkCur, bkCur,
    bkCur, bkCur, bkErr, bkErr, bkVar, bkErr, bkAny), (bkErr, bkErr, bkErr, bkErr, bkErr,
    bkChr, bkStr, bkVar, bkErr, bkAny), (bkErr, bkErr, bkErr, bkErr, bkErr, bkStr, bkStr, bkVar, bkErr, bkAny),
    (bkVar, bkVar, bkVar, bkVar, bkVar, bkVar, bkVar, bkVar, bkErr, bkAny), (bkErr, bkPtr, bkPtr,
    bkErr, bkErr, bkErr, bkErr, bkErr, bkPtr, bkAny), (bkAny, bkAny, bkAny, bkAny, bkAny, bkAny,
    bkAny, bkAny, bkAny, bkAny));
  IntBaseMaps: array[TIntKind] of TBaseKind = (bkInt, bkInt, bkInt, bkInt, bkInt, bkInt, bkBig, bkBig);
  NumBaseMaps: array[TNumericKind] of TBaseKind = (bkFlt, bkFlt, bkFlt, bkCur, bkFlt, bkFlt);
  BoolBaseMaps: array[TBoolKind] of TBaseKind = (bkBol,
    bkBol, bkBol, bkBol);
  CharBaseMaps: array[TCharKind] of TBaseKind = (bkChr, bkChr);

const
  BoolStr: array[boolean] of string = ('false', 'true');
  IntBoolStr: array[boolean] of string = ('0', '1');
  {ICmpOpMaps: array[opcNE..opcGE, Boolean] of string =
    (('icmp ne', 'icmp ne'), ('icmp eq', 'icmp eq'), ('icmp ult', 'icmp slt'), ('icmp ule', 'icmp sle'),
    ('icmp ugt', 'icmp sgt'), ('icmp uge', 'icmp sge'));}
  ArithOpMaps: array[opcADD..opcSHR] of string =
    ('add', 'sub', 'or', 'xor', 'mul', 'fdiv', 'div', 'urem', 'and', 'shl', 'lshr');

type
  TCastKind = (ckNone, ckError, ckITrunc, ckSExt, ckZExt, ckFpTrunc, ckFpExt, ckFp2Si, ckFp2Ui,
    ckSi2Fp, ckUi2Fp, ckCur2Si, ckSi2Cur, ckUi2Cur, ckFp2Cur, ckCur2Fp, ckInt2Bol, ckBol2Bol,
    ckPtr2Int, ckInt2Ptr, ckPtr2Ptr, ckAs2Ws, ckAs2Us, ckAs2Ss, ckWs2As, ckWs2Us, ckWs2Ss, ckUs2As,
    ckUs2Ws, ckUs2Ss, ckSs2As, ckSs2Ws, ckSs2Us, ckAc2As, ckAc2Ws, ckAc2Us, ckAc2Ss, ckWc2As, ckWc2Ws,
    ckWc2Us, ckWc2Ss);
  TCastBaseType = (cbtNone, cbtInt8, cbtUInt8, cbtInt16, cbtUInt16, cbtInt32, cbUInt32, cbtInt64,
    cbtUInt64, cbtComp, cbtFP32, cbtFP64, cbtFP80, cbtCurr, cbtBool, cbtBool8, cbtBool16, cbtBool32,
    cbtAChr, cbtWChr, cbtPtr, cbtPAChr, cbtPWChr);

const
  IntToCBTs: array[TIntKind] of TCastBaseType = (cbtInt8, cbtUInt8, cbtInt16, cbtUInt16, cbtInt32, cbUInt32, cbtInt64, cbtUInt64);
  NumToCBTs: array[TNumericKind] of TCastBaseType = (cbtFP32, cbtFP64, cbtFP80, cbtCurr, cbtComp, cbtFP64);
  BoolToCBTs: array[TBoolKind] of TCastBaseType = (cbtBool, cbtBool8, cbtBool16, cbtBool32);
  CharToCBTs: array[TCharKind] of TCastBaseType = (cbtAChr, cbtWChr);
  CastMaps: array[cbtInt8..cbtPWChr, cbtInt8..cbtPWChr] of TCastKind =
    ((ckNone, ckNone, ckSExt, ckSExt, ckSExt, ckSExt, ckSExt, ckSExt, ckSExt, ckSi2Fp, ckSi2Fp, ckSi2Fp,
    ckSi2Cur, ckInt2Bol, ckNone, ckSExt, ckSExt, ckNone, ckSExt, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckUi2Fp, ckUi2Fp,
    ckUi2Fp, ckUi2Cur, ckInt2Bol, ckNone, ckZExt, ckZExt, ckNone, ckZExt, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckITrunc, ckITrunc, ckNone, ckNone, ckSExt, ckSExt, ckSExt, ckSExt, ckSExt, ckSi2Fp, ckSi2Fp,
    ckSi2Fp, ckSi2Cur, ckInt2Bol, ckITrunc, ckNone, ckSExt, ckITrunc, ckNone, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckITrunc, ckITrunc, ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckUi2Fp, ckUi2Fp,
    ckUi2Fp, ckUi2Cur, ckInt2Bol, ckITrunc, ckNone, ckZExt, ckITrunc, ckNone, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckNone, ckNone, ckSExt, ckSExt, ckSExt, ckSi2Fp,
    ckSi2Fp, ckSi2Fp, ckSi2Cur, ckInt2Bol, ckITrunc,
    ckITrunc, ckNone, ckITrunc, ckITrunc, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckUi2Fp,
    ckUi2Fp, ckUi2Fp, ckUi2Cur, ckInt2Bol, ckITrunc, ckITrunc, ckNone, ckITrunc, ckITrunc, ckInt2Ptr,
    ckInt2Ptr, ckInt2Ptr), (ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckNone,
    ckNone, ckNone, ckSi2Fp, ckSi2Fp, ckSi2Fp, ckSi2Cur, ckInt2Bol, ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckITrunc,
    ckInt2Ptr, ckInt2Ptr, ckInt2Ptr), (ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckITrunc,
    ckNone, ckNone, ckNone, ckUi2Fp, ckUi2Fp, ckUi2Fp, ckUi2Cur, ckInt2Bol, ckITrunc, ckITrunc,
    ckITrunc, ckITrunc, ckITrunc, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr), (ckITrunc, ckITrunc, ckITrunc,
    ckITrunc, ckITrunc, ckITrunc, ckNone, ckNone, ckNone, ckSi2Fp, ckSi2Fp, ckSi2Fp, ckSi2Cur,
    ckInt2Bol, ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckNone,
    ckFpExt, ckFpExt, ckFp2Cur, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError),
    (ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFpTrunc,
    ckNone, ckNone, ckFp2Cur, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError),
    (ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFp2Ui, ckFp2Si, ckFpTrunc,
    ckNone, ckNone, ckFp2Cur, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError),

    (ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckCur2Si, ckCur2Fp,
    ckCur2Fp, ckCur2Fp, ckNone, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError, ckError),
    (ckNone, ckNone,
    ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckError, ckError, ckError, ckError,
    ckNone, ckBol2Bol, ckBol2Bol, ckBol2Bol, ckZExt, ckZExt, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckError, ckError,
    ckError, ckError, ckInt2Bol, ckNone, ckBol2Bol, ckBol2Bol, ckNone, ckZExt, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckITrunc, ckITrunc, ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt, ckError, ckError,
    ckError, ckError, ckInt2Bol, ckBol2Bol, ckNone, ckBol2Bol, ckITrunc, ckNone, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr),
    (ckITrunc, ckITrunc, ckITrunc, ckITrunc, ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckError,
    ckError, ckError, ckError, ckInt2Bol, ckBol2Bol, ckBol2Bol, ckNone, ckITrunc, ckITrunc,
    ckInt2Ptr, ckInt2Ptr, ckInt2Ptr), (ckNone, ckNone, ckZExt, ckZExt, ckZExt, ckZExt, ckZExt,
    ckZExt, ckZExt, ckUi2Fp, ckUi2Fp, ckUi2Fp, ckUi2Cur, ckInt2Bol, ckNone, ckZExt, ckZExt, ckNone,
    ckZExt, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr), (ckITrunc, ckITrunc, ckNone, ckNone, ckZExt, ckZExt,
    ckZExt, ckZExt, ckZExt, ckUi2Fp, ckUi2Fp, ckUi2Fp, ckUi2Cur, ckInt2Bol, ckITrunc,
    ckNone, ckZExt, ckITrunc, ckNone, ckInt2Ptr, ckInt2Ptr, ckInt2Ptr), (ckPtr2Int, ckPtr2Int,
    ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckError, ckError,
    ckError, ckError, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Ptr,
    ckPtr2Ptr, ckPtr2Ptr),
    (ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int,
    ckPtr2Int, ckError, ckError, ckError, ckError, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int,
    ckPtr2Int, ckPtr2Int, ckPtr2Ptr, ckNone, ckPtr2Ptr), (ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int,
    ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckError, ckError, ckError, ckError,
    ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Int, ckPtr2Ptr, ckPtr2Ptr, ckNone));

function IsStructType(T: TType): boolean;
begin
  T := T.OriginalType;
  case T.TypeCode of
    typSet: Result := T.Size > 4;
    typString: Result := TStringType(T).Kind in [strWShort, strAShort];
    else
      Result := T.TypeCode in StructTypes;
  end;
end;

function NeedInit(T: TType): boolean;
begin
  case T.TypeCode of
    typArray: Result := staNeedInit in TArrayType(T).ArrayAttr;
    typRecord: Result := staNeedInit in TRecordType(T).RecordAttr;
    typString: Result := not (TStringType(T).Kind in [strAShort, strWShort]);
    else
      Result := T.TypeCode in AutoInitTypes;
  end;
end;

function NeedFree(T: TType): boolean;
begin
  case T.TypeCode
    of
    typArray: Result := staNeedInit in TArrayType(T).ArrayAttr;
    typRecord: Result := staNeedInit in TRecordType(T).RecordAttr;
    typString: Result := not (TStringType(T).Kind in [strAShort, strWShort]);
    else
      Result := T.TypeCode in AutoFreeTypes;
  end;
end;

function InitTabVar(T: TType): string;
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
begin
  Result := Format('%s.$init', [T.Name]);
end;

function InitTabType(T: TType): string;
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
begin
  Result := Format('%s.$init.t', [T.Name]);
end;

function MangledName(Sym: TSymbol): string;
begin
  Result := '';
  while Sym <> nil do
  begin
    if Result <> '' then
      Result := '.' + Result;
    if (Sym.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) and TFunctionDecl(Sym).IsOverload then
      Result := Sym.Name + '$' + IntToStr(TFunctionDecl(Sym).ID)
    else
      Result := Sym.Name + Result;
    Sym := Sym.Parent;
  end;
end;

function LastChar(const s: string): char;
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
begin
  if s <> '' then
    Result := s[Length(s)]
  else
    Result := #0;
end;

procedure RemoveLastChar(var s: string);
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
  overload;
begin
  if s <> '' then
    Delete(s, Length(s), 1);
end;

procedure RemoveLastChar(var s: string; Count: integer);
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
  overload;
begin
  if s <> '' then
    Delete(s, Length(s) - Count + 1, Count);
end;

function EncodeWStr(const s: WideString): ansistring;
var
  I: integer;
  C: widechar;
begin
  Result := '';
  for I := 1 to Length(s) do
  begin
    C := s[I];
    Result := Result + 'i16 ' + IntToStr(word(C)) + ',';
  end;
  Result := Result + 'i16 0';
end;

function EncodeAStr(const s: ansistring; TailNullChar: boolean = True): ansistring;
var
  I: integer;
  C: AnsiChar;
begin
  Result := s;
  for I := Length(Result) downto 1 do
  begin
    C := Result[I];
    if (C < #32) or (C > #126) then
      Insert(Format('%.2x', [Ord(C)]), Result, I + 1);
  end;
  if TailNullChar then
    Result := Result + '\00';
end;

var
  llvmIntTypeStrs: array[0..7] of string = ('i1', 'i8', 'i16', 'i32', 'i64', 'i128', '%SizeInt', '%NativeInt');
  llvmFloatTypeStrs: array[0..2] of string = ('float', 'double', '%LongDouble');

procedure EnsureType(const TypStr: string; typeList: array of string; const msg: string); overload;
var
  i: integer;
begin
  for i := 0 to Length(typeList) - 1 do
    if TypStr = typeList[i] then
      Exit;
  raise ECodeGenError.Create(msg);
end;

procedure EnsureType(const TyStr1, TyStr2: string; const msg: string);
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
  overload;
begin
  if TyStr1 <> TyStr2 then
    raise ECodeGenError.Create(msg);
end;

procedure EnsurePtr(const desT, msg: string);
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
  overload;
begin
  if LastChar(desT) <> '*' then
    raise ECodeGenError.Create(msg);
end;

procedure EnsurePtr(const desT, msg: string; const Args: array of const); overload;
begin
  if LastChar(desT) <> '*' then
    raise ECodeGenError.CreateFmt(msg, Args);
end;

function DecodeTyStr(const S: string): TLLVMIntType;
{$IFNDEF DEBUG}
  inline;
{$ENDIF}
begin
  if S = 'i8' then
    Result := ltI8
  else if S = 'i16' then
    Result := ltI16
  else if S = 'i32' then
    Result := ltI32
  else if S = 'i64' then
    Result := ltI64
  else
    Result := ltI32;
end;

procedure VarInfoCopy(const Src: TVarInfo; out Dest: TVarInfo);
begin
  Dest.Name := Src.Name;
  Dest.TyStr := Src.TyStr;
  Dest.States := Src.States;
  Dest.Align := Src.Align;
end;

procedure VarInfoInit(out V: TVarInfo);
begin
  V.Name := '';
  V.TyStr := '';
  V.States := [];
  V.Align := '';
end;

procedure TCodeGen.AddExternalSymbol(Sym: TSymbol);
begin
  if Sym = nil then
    Exit;
  if Sym.Module <> FModule then
  begin
    FExternalSymbols.Add(Sym, nil);
  end;
end;

procedure TCodeGen.AddInitWStr(const VarName, DataVarName, DataTyStr: string);
var
  wsInit: TWStrInitInfo;
begin
  wsInit := TWStrInitInfo.Create;
  wsInit.VarName := VarName;
  wsInit.DataVarName := DataVarName;
  wsInit.DataTyStr := DataTyStr;
  FWStrInitList.Add(wsInit);
end;

procedure TCodeGen.AddSystemRoutine(Routine: TSystemRoutine);
begin
  AddExternalSymbol(FContext.GetSystemRoutine(Routine));
end;

function TCodeGen.ArgDeclStr(Arg: TFuncParam; NeedName: boolean): string;
var
  T: TType;
  ByRef: boolean;
begin
  ByRef := False;
  T := Arg.ParamType;
  if T.TypeCode = typUntype then
  begin
    Result := 'i8*';
    ByRef := True;
  end
  else
  begin
    Result := TypeStr(T);
    if IsStructType(T) or (Arg.Modifier in [argOut, argVar]) then
    begin
      Result := Result + '*';
      ByRef := Arg.Modifier <> argDefault;
    end;
  end;
  if NeedName then
  begin
    Result := Result + ' %' + Arg.Name;
    if ByRef then
      Result := Result + '.addr';
  end;
end;

function TCodeGen.ArgTypeStr(T: TType; Modifier: TArgumentModifier): string;
begin
  if (T = nil) or (T.TypeCode = typUntype) then
  begin
    Result := 'i8*';
    Exit;
  end;
  Result := TypeStr(T);
  if IsStructType(T) or (Modifier in [argOut, argVar]) then
    Result := Result + '*';
end;

function TCodeGen.CCStr(cc: TCallingConvention): string;
const
  x86_cc: array[TCallingConvention] of string = ('fastcc', 'fastcc', 'ccc', 'ccc', 'cc 64', 'ccc');
  other_cc: array[TCallingConvention] of string = ('fastcc', 'fastcc', 'ccc', 'ccc', 'ccc', 'ccc');
begin
  if CPU in [ckX86, ckX86_64] then
    Result := x86_cc[cc]
  else
    Result := other_cc[cc];
  DefCC := 'fastcc';
end;

procedure TCodeGen.ClearWStrInitList;
var
  i: integer;
begin
  for i := 0 to FWStrInitList.Count - 1 do
    TObject(FWStrInitList[i]).Free;
  FWStrInitList.Clear;
end;

constructor TCodeGen.Create(ACntx: TCompileContext);
begin
  FContext := ACntx;
  FCodes := TStringList.Create;
  FCodes.Capacity := 128;
  FDecls := TStringList.Create;
  FDecls.Capacity := 128;
  FExtDecls := TStringList.Create;
  FExtDecls.Capacity := 128;
  FStrConstList := THashTable.Create(100, True);
  FSetConstList := THashTable.Create(50, False);
  FExternalSymbols := TPtrHashTable.Create;
  FEmittedSymbols := TPtrHashTable.Create;
  FWStrInitList := TFPList.Create;
  FWStrInitList.Capacity := 16;
  FCntxList := TFPList.Create;
  FCntxList.Capacity := 16;
  {$ifdef CPU64}
  NativeIntStr := 'i64';
  LongDoubleStr := 'double';
  CPU := ckX86_64;
  {$else}
  {$ifdef CPU386}
  NativeIntStr := 'i32';
  LongDoubleStr := 'x86_fp80';
  CPU := ckX86;
  {$endif}
  {$endif}
end;

function TCodeGen.CurLandingPad: string;
begin
  with FCurCntx do
  begin
    if LandingpadStack.Count > 0 then
      Result := LandingpadStack[LandingpadStack.Count - 1]
    else
      Result := '';
  end;
end;

destructor TCodeGen.Destroy;
begin
  FCodes.Free;
  FDecls.Free;
  FExtDecls.Free;
  FStrConstList.Free;
  FSetConstList.Free;
  FExternalSymbols.Free;
  FEmittedSymbols.Free;
  FCntxList.Free;
  ClearWStrInitList;
  FWStrInitList.Free;
  inherited Destroy;
end;

procedure TCodeGen.Emit(Func: TFunction);
var
  cs: TCodePack;
begin
  cs := TCodePack.Create;
  try
    cs.StrConstList := FStrConstList;
    cs.SetConstList := FSetConstList;
    cs.Setup(FContext, Func);
    EmitFunc(Func);
  finally
    cs.Free;
  end;
end;

procedure TCodeGen.EmitBuiltin(E: TBinaryOp; Func: TBuiltinFunction; Args: TListOp; var Result: TVarInfo);
var
  A1, A2, A3: TBaseOp;
  V1, V2, V3: TVarInfo;
  Num: integer;
  Va, Va2, Va3: string;

  procedure EmitBuiltin_Abs;
  begin
    case
      A1.Typ.BaseCode of
      btcShortint, btcSmallint, btcLongint, btcInt64, btcComp, btcCurrency:
      begin
        Va := TempVar;
        WriteCode('%s = icmp slt %s %s, 0', [Va, V1.TyStr, V1.Name]);
        Va2 := TempVar;
        WriteCode('%s = sub i32 0, %s', [Va2, V1.Name]);
        Va3 := TempVar;
        WriteCode('%s = select i1 %s, %s %s, %s %s', [Va3, Va, V1.TyStr, Va2, V1.TyStr, V1.Name]);
        Result.Name := Va3;
        Result.TyStr := V1.TyStr;
        Result.States := [];
      end;
      btcByte, btcWord, btcLongWord, btcUInt64:
      begin
        Result.Name := V1.Name;
        Result.TyStr := V1.TyStr;
        Result.States := V1.States;
      end;
      btcSingle:
      begin
        Va := TempVar;
        WriteCode('%s = call @llvm.fabs.f32(float %s)', [Va, V1.Name]);
        Result.Name := Va;
        Result.TyStr := V1.TyStr;
        Result.States := [];
      end;
      btcReal48, btcDouble, btcExtended:
      begin
        Va := TempVar;
        WriteCode('%s = call @llvm.fabs.f64(double %s)', [Va, V1.Name]);
        Result.Name := Va;
        Result.TyStr := V1.TyStr;
        Result.States := [];
      end;
      else
        Assert(False);
    end;
  end;

  function IntTy(T: TType): TLLVMIntType;
  begin
    case T.Size of
      1: Result := ltI8;
      2: Result := ltI16;
      4: Result := ltI32;
      8: Result := ltI64;
      else
        Assert(False);
        Result := ltI8;
    end;
  end;

  procedure EmitBuiltin_AddSub(out Result: TVarInfo; DoAdd: boolean; const DeltaVa: string = '1');
  var
    D1: TVarInfo;
  begin
    EmitOp_VarLoad(V1, D1);
    if cdOverflowChecks in E.Switches then
    begin
      V2.Name := DeltaVa;
      V2.TyStr := D1.TyStr;
      V2.States := [];
      Result.Name := '';
      if DoAdd then
        EmitOp_IntOvf(D1, V2, Result, opcADD, IntTy(A1.Typ), True)
      else
        EmitOp_IntOvf(D1, V2, Result, opcSUB, IntTy(A1.Typ), True);
    end
    else
    begin
      Va := TempVar;
      if DoAdd then
        WriteCode('%s = add %s %s, %s', [Va, D1.TyStr, D1.Name, DeltaVa])
      else
        WriteCode('%s = sub %s %s, %s', [Va, D1.TyStr, D1.Name, DeltaVa]);
      Result.Name := Va;
      Result.TyStr := D1.TyStr;
      Result.States := [];
    end;
    if (cdRangeChecks in E.Switches) and (A1.Typ.BaseCode in [btcBoolean, btcSubrange]) then
      EmitRangeCheck(Result, A1.Typ, A1.Typ);
  end;

  procedure EmitBuiltin_IncDecPtr(DoInc: boolean);
  var
    Va: string;
    D1: TVarInfo;
  begin
    if Num > 1 then
    begin
      EmitOp_VarLoad(V2);
      EmitCast(V2, A2.Typ, FContext.FNativeIntType);
      if not DoInc then
      begin
        Va := TempVar;
        WriteCode('%s = sub %s 0, %s', [Va, Self.NativeIntStr, V2.Name]);
        V2.Name := Va;
        V2.TyStr := NativeIntStr;
      end;
    end
    else
    begin
      if DoInc then
        V2.Name := '1'
      else
        V2.Name := '-1';
      V2.TyStr := Self.NativeIntStr;
      V2.States := [];
    end;
    EmitOp_VarLoad(V1, D1);
    Result.Name := TempVar;
    Result.TyStr := D1.TyStr;
    Result.States := [];
    WriteCode('%s = getelementptr %s, %s %s, %s %s', [Result.Name, D1.TyStr.Replace('*', '') +
      StringOfChar('*', D1.TyStr.CountChar('*') - 1), D1.TyStr, D1.Name, V2.TyStr, V2.Name]);
    WriteCode('store %s %s, %s %s', [Result.TyStr, Result.Name, V1.TyStr, V1.Name]);
  end;

  procedure EmitBuiltin_IncDec(DoInc: boolean);
  var
    Ret: TVarInfo;
  begin
    if Num > 1 then
    begin
      EmitOp_VarLoad(V2);
      EmitCast(V2, A2.Typ, A1.Typ);
    end
    else
    begin
      V2.Name := '1';
      V2.TyStr := TypeStr(A1.Typ);
      V2.States := [];
    end;
    EmitBuiltin_AddSub(Ret, DoInc, V2.Name);
    WriteCode('store %s %s, %s %s', [Ret.TyStr, Ret.Name, V1.TyStr, V1.Name]);
  end;

  procedure EmitBuiltin_Chr;
  begin
    Assert(A1.Typ.NormalType.TypeCode = typInt, 'EmitBuiltin_Chr');
    EmitCast(V1, A1.Typ, FContext.FCharType);
    VarInfoCopy(V1, Result);
  end;

  procedure EmitBuiltin_Ord;
  begin
    EmitOp_VarLoad(V1);
    VarInfoCopy(V1, Result);
  end;

  procedure EmitBuiltin_Addr;
  begin
    VarInfoCopy(V1, Result);
    if vasAddrOfVar in Result.States then
    begin
      Exclude(Result.States, vasAddrOfVar);
      Include(Result.States, vasAddrValue);
    end
    else
      EmitError(E.Coord, 'EmitBuiltin_Addr: expected address of variable');
  end;

  procedure EmitBuiltin_Ptr;
  begin
    Assert(A1.Typ.NormalType.TypeCode = typInt, 'EmitBuiltin_Ptr');
    EmitIns_Int2Ptr(V1, 'i8*');
    VarInfoCopy(V1, Result);
  end;

  procedure EmitBuiltin_GetMem;
  begin
    Assert(A1.Typ.NormalType.IsPointer);
    Assert(A2.Typ.NormalType.IsInteger);
    EmitIns_Bitcast(V1, 'i8**');
    Self.EmitOp_VarLoad(V2);
    Self.EmitCast(V2, A2.Typ, FContext.FNativeIntType);
    Va := TempVar;
    WriteCode('%s = tail call noalias i8* @malloc(%s %s) nounwind', [Va, V2.TyStr, V2.Name]);
    WriteCode('store i8* %s, i8** %s', [Va, V1.Name]);
    Include(FIntrinsics, llvm_malloc);
  end;

  procedure EmitBuiltin_FreeMem;
  begin
    assert(A1.Typ.NormalType.IsPointer);
    Self.EmitOp_VarLoad(V1);
    EmitIns_Bitcast(V1, 'i8*');
    WriteCode('tail call void @free(i8* %s) nounwind', [V1.Name]);
    Include(FIntrinsics, llvm_free);
  end;

var
  ActualArgs: TListOp;
begin
  Num := 0;
  A1 := nil;
  A2 := nil;
  A3 := nil;
  V1.States := [];
  V3.States := [];
  ActualArgs := TListOp(E.Right);
  Num := ActualArgs.Count;
  if Num > 0 then
    A1 := ActualArgs.Items[0];
  if Num > 1 then
    A2 := ActualArgs.Items[1];
  if Num > 2 then
    A3 := ActualArgs.Items[2];
  if A1 <> nil then
    EmitOp(A1, V1);
  if A2 <> nil then
    EmitOp(A2, V2);
  if A3 <> nil then
    EmitOp(A3, V3);
  case Func.Kind of
    bfAbs:
      EmitBuiltin_Abs;
    bfAddr: EmitBuiltin_Addr;
    bfChr: EmitBuiltin_Chr;
    bfDec: if A1.Typ.IsPointer then
        EmitBuiltin_IncDecPtr(False)
      else
        EmitBuiltin_IncDec(False);
    bfGetMem: EmitBuiltin_GetMem;
    bfFreeMem: EmitBuiltin_FreeMem;
    bfInc: if A1.Typ.IsPointer then
        EmitBuiltin_IncDecPtr(True)
      else
        EmitBuiltin_IncDec(True);
    bfOrd: EmitBuiltin_Ord;
    bfPred: EmitBuiltin_AddSub(Result, False);
    bfSucc: EmitBuiltin_AddSub(Result, True);
    bfPtr: EmitBuiltin_Ptr;
    bfNoop:
    begin
    end;
    else
      Assert(False);
  end;
end;

procedure TCodeGen.EmitCall(Func: TFunctionDecl; const Typs, Args: array of string; const RetVar: string);
var
  argStr, lpad, s, retty, nextLabel: string;
  i: integer;
begin
  Assert(High(Typs) = High(Args), 'EmitCall, Typs <> Args');
  Assert(Func.CallConvention <> ccSafecall, 'EmitCall, safecall not allow');
  ArgStr := '';
  for i := 0 to High(Typs) do
  begin
    argStr := argStr + Format('%s %s, ', [Typs[i], Args[i]]);
  end;
  if argStr <> '' then
    Delete(argStr, Length(argStr) - 1, 2);
  if not Assigned(Func.ReturnType) or IsSpecialType(Func.ReturnType) then
    retty := 'void'
  else
    retty := TypeStr(Func.ReturnType);
  if retVar = '' then
    S := ''
  else
    S := RetVar + ' = ';
  lpad := Self.CurLandingPad;
  if lpad = '' then
  begin
    WriteCode('%scall ' + retty.Replace('*', '') + StringOfChar('*', retty.CountChar('*') -
      1) + ' %s @%s(%s)', [S, CCStr(Func.CallConvention), retty, MangledName(Func), argStr]);
  end
  else
  begin
    nextLabel := Self.LabelStr('next.');
    WriteCode('%sinvoke %s %s @%s(%s) to label %%%s unwind label %%%s',
      [S, CCStr(Func.CallConvention), retty, MangledName(Func), argStr, nextLabel, lpad]);
    WriteLabel(nextLabel);
  end;
end;

procedure TCodeGen.EmitCallSys(Routine: TSystemRoutine; const Typs, Args: array of string; const RetVar: string);
begin
  AddExternalSymbol(FContext.GetSystemRoutine(Routine));
  EmitCall(FContext.GetSystemRoutine(Routine), Typs, Args, RetVar);
end;

procedure TCodeGen.EmitCast(var R: TVarInfo; RT, LT: TType; const debugStr: string);

  procedure EmitBitcast(var V: TVarInfo; const desT: string);
  var
    va: string;
  begin
    if V.TyStr <> desT then
    begin
      EnsurePtr(desT, 'EmitBitcast');
      EnsurePtr(V.TyStr, 'EmitBitcast');
      va := TempVar;
      WriteCode('%s = bitcast %s %s to %s', [va, V.TyStr, V.Name, desT]);
      V.Name := va;
      V.TyStr := desT;
    end;
  end;

  function CBT(T: TType): TCastBaseType;
  begin
    case T.TypeCode of
      typInt: Result := IntToCBTs[TIntType(T).Kind];
      typNumeric: Result := NumToCBTs[TNumericType(T).Kind];
      typBool: Result := BoolToCBTs[TBoolType(T).Kind];
      typChar: Result := CharToCBTs[TCharType(T).Kind];
      typPointer: Result := cbtPtr;
      typPAnsiChar: Result := cbtPAChr;
      typPWideChar: Result := cbtPWChr;
      typSubrange: Result := CBT(TSubrangeType(T).BaseType);
      typEnum: case T.Size of
          1: Result := cbtInt8;
          2: Result := cbtInt16;
          4: Result := cbtInt32;
          else
            Result := cbtInt64;
        end;
      typProcedural: Result := cbtPtr;
      typString: if TStringType(T).Kind in [strAnsi, strWide, strUnicode] then
          Result := cbtPtr
        else
          Result := cbtNone;
      typClass, typClassRef, typInterface, typDynamicArray: Result := cbtPtr;
      else
        Result := cbtNone
    end;
  end;

type
  TMPCastKind = (mpckNone, mpckPtr2MP, mpckMP2MP, mpckMP2Ptr);
const
  MethPtrCastMaps: array[boolean, boolean] of TMPCastKind = ((mpckNone, mpckPtr2MP), (mpckMP2Ptr, mpckMP2MP));

  procedure EmitPtr2MP(var R: TVarInfo);
  var
    va1, va2: string;
  begin
    va1 := TempVar;
    va2 := TempVar;
    if (R.Name = 'null') then
      WriteCode('%s = insertvalue [2 x i8*] undef, i8* null, 0', [va1])
    else
    begin
      EmitBitcast(R, 'i8*');
      WriteCode('%s = insertvalue [2 x i8*] undef, i8* %s, 0', [va1, R.Name]);
    end;
    WriteCode('%s = insertvalue [2 x i8*] %s, i8* null, 1', [va2, va1]);
    R.Name := va2;
    R.TyStr := '[2 x i8*]';
    R.States := [];
  end;

  procedure EmitMP2Ptr(var R: TVarInfo);
  var
    va1: string;
  begin
    EnsureType(R.TyStr, '[2 x i8*]', 'EmitMP2Ptr');
    va1 := TempVar;
    WriteCode('%s = extractvalue [2 x i8*] %s, 0', [va1, R.Name]);
    R.Name := va1;
    R.TyStr := 'i8*';
    R.States := [];
  end;

var
  ck: TCastKind;
  lcbt, rcbt: TCastBaseType;
begin
  if RT.TypeCode = typSubrange then
    RT := TSubrangeType(RT).BaseType;
  if LT.TypeCode = typSubrange then
    LT := TSubrangeType(LT).BaseType;
  if RT.Equals(LT) then
    Exit;
  lcbt := CBT(LT);
  rcbt := CBT(RT);
  if (lcbt > cbtNone) and (rcbt > cbtNone) then
  begin
    ck := CastMaps[rcbt, lcbt];
    case ck of
      ckITrunc: EmitIns_IntTrunc(R, TypeStr(LT));
      ckSExt: EmitIns_IntExt(R, TypeStr(LT), True);
      ckZExt: EmitIns_IntExt(R, TypeStr(LT), False);
      ckFpTrunc: EmitIns_FltTrunc(R, TypeStr(LT));
      ckFpExt: EmitIns_FltExt(R, TypeStr(LT));
      ckSi2Fp: EmitIns_Int2Flt(R, TypeStr(LT), True);
      ckUi2Fp: EmitIns_Int2Flt(R, TypeStr(LT), False);
      ckSi2Cur: EmitIns_Int2Cur(R, True);
      ckUi2Cur: EmitIns_Int2Cur(R, False);
      ckFp2Cur: EmitIns_Flt2Cur(R);
      ckCur2Fp: EmitIns_Cur2Flt(R, TypeStr(LT));
      ckCur2Si: EmitIns_Cur2Comp(R);
      ckInt2Bol: EmitIns_Int2Bol(R);
      ckBol2Bol: EmitIns_Bol2Bol(R, LT);
      ckPtr2Int: EmitIns_Ptr2Int(R, TypeStr(LT));
      ckInt2Ptr: EmitIns_Int2Ptr(R, TypeStr(LT));
      ckPtr2Ptr: case MethPtrCastMaps[RT.IsMethodPointer, LT.IsMethodPointer] of
          mpckPtr2MP: EmitPtr2MP(R);
          mpckMP2Ptr: EmitMP2Ptr(R);
          mpckMP2MP:
          begin
          end;
          else
            EmitBitcast(R, TypeStr(LT));
        end;
      ckNone:
      begin
      end;
      else
        Assert(False, 'EmitCast, invalid cast,' + debugStr);
    end;
  end
  else
    case LT.BaseCode of
      btcClass, btcClassRef, btcPointer, btcPAnsiChar, btcPWideChar, btcInterface, btcDispInterface,
      btcDynamicArray: if RT.BaseCode in [btcClass, btcClassRef, btcPointer, btcPAnsiChar,
          btcPWideChar, btcInterface, btcDispInterface, btcDynamicArray] then
        begin
          EmitBitcast(R, TypeStr(LT));
        end
        else
          Assert(False, 'EmitCast:' + debugStr);
      else
        Assert(False, 'EmitCast:' + Lt.Name + ',' + rt.Name + ',' + debugStr);
    end;
end;

procedure TCodeGen.EmitCmd(Cmd: TCmd; Pre: TCmd);

  procedure EmitJump(Jump: TJumpCmd);
  var
    va: TVarInfo;
  begin
    va.States := [];
    EmitOp(Jump.Condition, va);
    EmitIns_Bol2I1(va);
    WriteCode('br i1 %s, label %%%s, label %%%s', [va.Name, Jump.TrueTarget, Jump.FalseTarget]);
  end;

  procedure EmitGoto(Ins: TGotoCmd);
  begin
    WriteCode('br label %%%s', [Ins.Target]);
  end;

  procedure EmitMark(Mark: TMarkCmd; PreCmd: TCmd);
  begin
    if (PreCmd = nil) or not (PreCmd.Kind in [insGoto, insJump]) then
      WriteCode('br label %%%s', [Mark.LabelName]);
    WriteLabel(Mark.LabelName);
  end;

  procedure EmitAssign(Stmt: TAssignCmd);
  var
    LV, RV: TVarInfo;
  begin
    LV.States := [];
    RV.States := [];
    EmitOp(Stmt.Left, LV);
    EmitOp(Stmt.Right, RV);
    EmitOp_VarLoad(RV);
    if (cdRangeChecks in Stmt.Left.Switches) and IsRangeCheckNeeded(Stmt.Right.Typ, Stmt.Left.Typ) then
    begin
      EmitRangeCheck(RV, Stmt.Right.Typ, Stmt.Left.Typ);
    end;
    EmitCast(RV, Stmt.Right.Typ, Stmt.Left.Typ);
    if (Stmt.Right.Typ.TypeCode = typBool) and (RV.TyStr = 'i1') then
      EmitIns_Bit2Bol(RV);
    WriteCode('store %s %s, %s %s', [RV.TyStr, RV.Name, LV.TyStr, LV.Name]);
  end;

  procedure EmitSwitch(Cmd: TSwitchCmd);
  var
    Va1: TVarInfo;
    Entry: TSwitchEntry;
    i: integer;
  begin
    Va1.States := [];
    EmitOp(Cmd.Value, Va1);
    EmitOp_VarLoad(Va1);
    WriteCode('switch %s %s, label %%%s [', [Va1.TyStr, Va1.Name, Cmd.OtherwiseTarget]);
    for i := 0 to Cmd.EntryCount - 1 do
    begin
      Entry := Cmd.Entries[i];
      WriteCode('    %s %d, label %%%s', [Va1.TyStr, Entry.Value, Entry.Target]);
    end;
    WriteCode('  ]');
  end;

  procedure EmitInvoke(Cmd: TCallCmd);
  var
    V: TVarInfo;
  begin
    VarInfoInit(V);
    EmitOp_Call(TBinaryOp(Cmd.CallOp), V);
  end;

  procedure EmitLeaveBlock;
  var
    Lab: string;
  begin
    Lab := CurLandingPad;
    if Copy(Lab, 1, 11) = 'except.lpad' then
    begin
      Lab := Lab + '.leave';
      WriteCode('br label %' + Lab);
      WriteLabel(Lab);
    end;
    Self.LeaveLandingpad;
  end;

  procedure EmitEndExcept(Cmd: TEndExceptCmd);
  begin
    if Cmd.ExceptVar <> '' then
    begin
      WriteCode('tail call fastcc void @System._FreeExceptObject(i8** %%%s.addr)', [Cmd.ExceptVar]);
    end;
    WriteCode('tail call void @__cxa_end_catch()');
  end;

  procedure EmitRaise(Cmd: TRaiseCmd);
  var
    va: TVarInfo;
  begin
    Assert(Cmd.Exception <> nil, 'EmitRaise');
    va.States := [];
    EmitOp(Cmd.Exception, va);
    Self.EmitOp_VarLoad(va);
    EmitCallSys(srRaiseExcept, ['i8*'], [va.Name]);
  end;

  procedure EmitReraise(Cmd: TReraiseCmd);
  var
    LPad: string;
  begin
    LPad := Self.CurLandingPad;
    assert(Cmd.ExceptVar <> '', 'EmitReraise');
    WriteCode('store i8* null, i8** %%%s.addr', [Cmd.ExceptVar]);
    WriteCode('invoke void @__cxa_rethrow() noreturn to label %%lpad.unreachable unwind label %%%s', [LPad]);
    FCurCntx.UnreachableUsed := True;
  end;

  procedure EmitOAInit(Cmd: TOAInitCmd);
  var
    i: integer;
    va, arr: TVarInfo;
    v1, ty: string;
  begin
    ty := TypeStr(Cmd.ArrayVar.VarType);
    arr.States := [];
    EmitOp_LoadRef(Cmd.ArrayVar, arr);
    for i := 0 to Cmd.ElementCount - 1 do
    begin
      va.States := [];
      EmitOp(Cmd.Elements[i], va);
      EmitOp_VarLoad(va);
      v1 := TempVar;
      WriteCode('%s = getelementptr %s, %s %s, %%SizeInt 0, %%SizeInt %d',
        [v1, TY.Replace('*', '') + StringOfChar('*', TY.CountChar('*') - 1), TY, arr.Name, i]);
      WriteCode('store %s %s, %s* %s', [ty, va.Name, ty, v1]);
    end;
  end;

begin
  case Cmd.Kind of
    insJump: EmitJump(TJumpCmd(Cmd));
    insAssign: EmitAssign(TAssignCmd(Cmd));
    insSwitch: EmitSwitch(TSwitchCmd(Cmd));
    insCall: EmitInvoke(TCallCmd(Cmd));
    insGoto: EmitGoto(TGotoCmd(Cmd));
    insMark: EmitMark(TMarkCmd(Cmd), Pre);
    insUninitVar:
    begin
      Assert(FCurCntx.Level > 0);
      Self.EmitVarUninit(TEmitFuncContext(FCntxList[FCurCntx.Level - 1]).Func);
    end;
    insCleanup: Self.EnterLandingpad(Cmd);
    insHandleExcept, insHandleCtorExcept, insHandleScExcept:
      Self.EnterLandingpad(Cmd);
    insLeaveBlock: EmitLeaveBlock;
    insEndExcept: EmitEndExcept(TEndExceptCmd(Cmd));
    insRaise: EmitRaise(TRaiseCmd(Cmd));
    insReraise: EmitReraise(TReraiseCmd(Cmd));
    insOAInit: EmitOAInit(TOAInitCmd(Cmd));
    else
      assert(False, 'EmitCmd');
  end;
end;

procedure TCodeGen.EmitCmdOfOp(E: TBaseOp);
var
  i: integer;
begin
  if E.CmdCount > 0 then
    EmitCmd(E.Cmds[0], nil);
  for i := 1 to E.CmdCount - 1 do
    EmitCmd(E.Cmds[I], E.Cmds[I - 1]);
end;

procedure TCodeGen.EmitCmds(List: TFPList);
var
  I: integer;
begin
  if List.Count > 0 then
    EmitCmd(TCmd(List[0]), nil);
  for I := 1 to List.Count - 1 do
    EmitCmd(TCmd(List[I]), TCmd(List[I - 1]));
end;

procedure TCodeGen.EmitError(const Msg: string; const Args: array of const);
begin
  EmitError(Format(Msg, Args));
end;

procedure TCodeGen.EmitError(const Msg: string);
begin
  raise ECodeGenError.Create(Msg);
end;

procedure TCodeGen.EmitError(const Coord: TAstNodeCoord; const Msg: string; const Args: array of const);
begin
  EmitError(Format('%s: %d,%d: %s', [ExtractFileName(Coord.FileName), Coord.Row, Coord.Col, Format(Msg, Args)]));
end;

procedure TCodeGen.EmitError(const Coord: TAstNodeCoord; const Msg: string);
begin
  EmitError(Format('%s: %d,%d: %s', [ExtractFileName(Coord.FileName), Coord.Row, Coord.Col, Msg]));
end;

procedure TCodeGen.EmitExternalDecl;

  procedure EmitExternalVarDecl(V: TVariable);
  begin
    WriteDecl(Format('@%s = external global %s', [MangledName(V), TypeStr(V.VarType)]));
  end;

  procedure EmitExternalTypeDecl(T: TType);
  begin
    case T.TypeCode
      of
      typClass: EmitRtti_Class_External(TClassType(T));
    end;
  end;

  procedure EmitExternalFuncDecl(F: TFunctionDecl);
  begin
    WriteDecl('declare ' + FuncDecl(F, False));
  end;

var
  I: integer;
  Sym: TSymbol;
  OldDecls: TStringList;
begin
  OldDecls := FDecls;
  FDecls := FExtDecls;
  for I := 0 to FExternalSymbols.Count - 1 do
  begin
    Sym := TSymbol(FExternalSymbols.Keys[I]);
    case
      Sym.NodeKind of
      nkVariable: EmitExternalVarDecl(TVariable(Sym));
      nkType: EmitExternalTypeDecl(TType(Sym));
      nkFunc, nkMethod, nkExternalFunc: EmitExternalFuncDecl(TFunctionDecl(Sym));
    end;
  end;
  FDecls := OldDecls;
end;

procedure TCodeGen.EmitExternals;
var
  typ: TIntKind;
begin
  if not SameText(FModule.Name, 'System') then
  begin
    for typ := Low(TIntKind) to High(TIntKind) do
    begin
      WriteDecl('@System.%s.$typeinfo = external global i8*', [ast.IntTypeNames[typ]]);
    end;
    WriteDecl('@System.Integer.$typeinfo = external global i8*');
    WriteDecl('@System.Cardinal.$typeinfo = external global i8*');
    WriteDecl('@System.String.$typeinfo = external global i8*');
    WriteDecl('@System.AnsiString.$typeinfo = external global i8*');
    WriteDecl('@System.WideString.$typeinfo = external global i8*');
    WriteDecl('@System.UnicodeString.$typeinfo = external global i8*');
  end;
  EmitExternalDecl;
end;

procedure TCodeGen.EmitFunc(Func: TFunctionDecl);

  function AddRefRoutine(typ: TType): TSystemRoutine;
  begin
    Result := srTrunc;
    case typ.TypeCode of
      typString: case TStringType(typ).Kind of
          strAnsi: Result := srAStrAddRef;
          strWide: Result := srWStrAddRef;
          strUnicode: Result := srUStrAddRef;
          else
            Assert(False, 'AddRefRoutine');
        end;
      typDynamicArray: Result := srDynArrayAddRef;
      typInterface: Result := srIntfAddRef;
      typVariant: Result := srVarAddRef;
      else
        Assert(False, 'AddRefRoutine');
    end;
  end;

  procedure ArgInit(Arg: TFuncParam);
  var
    ty, s: string;
    align: byte;
  begin
    if not (saUsed in Arg.Attr) then
      Exit; 
    ty := TypeStr(Arg.ParamType);
    align := Arg.ParamType.AlignSize;
    if FCurCntx.NeedFrame and (asNestRef in Arg.States) then
    begin
      if asByRef in Arg.States then
      begin
        s := TempVar;
        WriteCode('%s = getelementptr %s, %s* %%.fp, %%SizeInt 0, %%SizeInt %d', [s, FCurCntx.FrameTyStr, Arg.Index]);
        WriteCode('store %s* %%%s.addr, %s** %s', [ty, Arg.Name, ty, s]);
      end
      else
        WriteCode('%%%s.addr = getelementptr %s, %s* %%.fp, %%SizeInt 0, %%SizeInt %d',
          [Arg.Name, FCurCntx.FrameTyStr, Arg.Index]);
    end
    else if not (asByRef in Arg.States) then
      WriteCode('%%%s.addr = alloca %s, align %d', [Arg.Name, ty, align])
        //WriteCode('%%%s.addr = alloca %s', [Arg.Name, ty])
    else
      Exit;
    if asStructValue in Arg.States then
    begin
      EmitIns_memcpy(ty + '*', '%' + Arg.Name + '.addr', ty + '*', '%' + Arg.Name, Arg.ParamType.Size);
      case Arg.ParamType.TypeCode of
        typRecord, typObject: if staNeedInit in TRecordType(Arg.ParamType).RecordAttr then
          begin
            s := TempVar;
            WriteCode('%s = bitcast %s* %%%s.addr to i8*', [s, ty, Arg.Name]);
            WriteCode(
              'call %s void @System._RecordAddRef(i8* %s, i8* bitcast(%%%s.$init.t* @%s.$init to i8*))',
              [DefCC, s, Arg.ParamType.Name, Arg.ParamType.Name]);
          end;
        typArray: if staNeedInit in TArrayType(Arg.ParamType).ArrayAttr then
          begin
            s := TempVar;
            WriteCode('%s = bitcast %s* %%%s.addr to i8*', [s, ty, Arg.Name]);
            WriteCode('call %s void @System._ArrayAddRef(i8* %s, i8* bitcast(%%%s.$init.t* @%s.$init to i8*))',
              [DefCC, s, Arg.ParamType.Name, Arg.ParamType.Name]);
          end;
        typVariant:
        begin
          WriteCode(
            'call %s void @System._VarCopy(%System.TVarData* %%%s.addr, %System.TVarData* %%%s)',
            [DefCC, Arg.Name, Arg.Name]);
        end;
      end;
    end
    else if not (asByRef in Arg.States) then
    begin
      WriteCode('store %s %%%s, %s* %%%s.addr', [ty, Arg.Name, ty, Arg.Name]);
      case Arg.ParamType.TypeCode of
        typString, typInterface, typDynamicArray: if (Arg.Modifier = argDefault) and not
            ((Arg.ParamType.TypeCode = typString) and (TStringType(Arg.ParamType).Kind in [strAShort, strWShort])) then
          begin
            Self.EmitCallSys(AddRefRoutine(Arg.ParamType), [ty + '*'], ['%' + Arg.Name + '.addr']);
          end;
      end;
    end;
    WriteCodeNI('');
  end;

  procedure VarInit(V: TVariable);
  var
    s, ty: string;
  begin
    if not (saUsed in V.Attr) then
      Exit;
    if not (vaLocal in V.VarAttr) then
    begin
      Self.EmitGlobalVarDecl(V);
      Exit;
    end;
    ty := TypeStr(V.VarType);
    if FCurCntx.NeedFrame and (vsNestRef in V.States) then
    begin
      if vsResultAddr in V.States then
      begin
        s := TempVar;
        WriteCode('%s = getelementptr %%%s.$frame, %%%s.$frame* %%.fp, %%SizeInt 0, %%SizeInt %d',
          [s, FCurCntx.MangledName, FCurCntx.MangledName, V.Index]);
        WriteCode('store %s* %%Result.addr, %s** %s', [ty, ty, s]);
      end
      else if (vaSelf in V.VarAttr) then
      begin
        s := TempVar;
        WriteCode('%s = getelementptr %%%s.$frame, %%%s.$frame* %%.fp, %%SizeInt 0, %%SizeInt %d',
          [s, FCurCntx.MangledName, FCurCntx.MangledName, V.Index]);
        WriteCode('store i8* %Self, i8** ' + s);
      end
      else
        WriteCode('%%%s.addr = getelementptr %%%s.$frame, %%%s.$frame* %%.fp, %%SizeInt 0, %%SizeInt %d',
          [V.Name, FCurCntx.MangledName, FCurCntx.MangledName, V.Index]);
    end
    else if not (vsResultAddr in V.States) then
    begin
      WriteCode('%%%s.addr = alloca %s, align %d', [V.Name, ty, V.VarType.AlignSize]);
        //WriteCode('%%%s.addr = alloca %s', [V.Name, ty]);
    end
    else
      Exit;
    case V.VarType.TypeCode of
      typString: case TStringType(V.VarType).Kind of
          strAnsi, strWide, strUnicode: WriteCode('store %s null, %s* %%%s.addr', [ty, ty, V.Name]);
          strAShort:
          begin
            s := TempVar;
            WriteCode('%s = bitcast %s* %%%s.addr to i8*', [s, ty, V.Name]);
            WriteCode('store i8 0, i8* %s', [s]);
          end;
          strWShort:
          begin
            s := TempVar;
            WriteCode('%s = bitcast %s* %%%s.addr to i16*', [s, ty, V.Name]);
            WriteCode('store i16 0, i16* %s', [s]);
          end;
        end;
      typInterface, typDynamicArray:
      begin
        WriteCode('store %s null, %s* %%%s.addr', [ty, ty, V.Name]);
      end;
      typVariant:
      begin
        s := TempVar;
        WriteCode('%s = bitcast %s* %%%s.addr to %%SizeInt*', [s, ty, V.Name]);
        WriteCode('store %%SizeInt 0, %%SizeInt* %s', [s]);
      end;
      typRecord: if staNeedInit in TRecordType(V.VarType).RecordAttr then
        begin
          s := TempVar;
          WriteCode('%s = bitcast %s* %%%s.addr to i8*', [s, ty, V.Name]);
          WriteCode('call %s void @System._RecordInit(i8* %s, i8* bitcast(%%%s.$init.t* @%s.$init to i8*))',
            [DefCC, s, V.Name, V.Name]);
        end;
      typArray: if staNeedInit in TArrayType(V.VarType).ArrayAttr then
        begin
          s := TempVar;
          WriteCode('%s = bitcast %s* %%%s.addr to i8*', [s, ty, V.Name]);
          WriteCode('call %s void @System._ArrayInit(i8* %s, i8* bitcast(%%%s.$init.t* @%s.$init to i8*))',
            [DefCC, s, V.Name, V.Name]);
        end;
    end;
    WriteCodeNI('');
  end;

  procedure WriteLocalInit(Func: TFunction);
  var
    i, parentLevel: integer;
    Sym: TSymbol;
    List: TFPList;
    Va1, parentFrame: string;
    parentCntx: TEmitFuncContext;
  begin
    if (FCurCntx.Level > 0) and FCurCntx.NeedFrame then
    begin
      parentLevel := FCurCntx.Level - 1;
      parentFrame := TEmitFuncContext(FCntxList[parentLevel]).FrameTyStr;
      Va1 := TempVar;
      WriteCode('%s = getelementptr %s, %s* %%.fp, %%SizeInt 0, %%SizeInt %d', [Va1, FCurCntx.FrameTyStr,
        FCurCntx.FrameTyStr, FCurCntx.LinkedFrameIndex]);
      WriteCode('store %s* %%.fp%d, %s** %s', [parentFrame, FCurCntx.Level - 1, parentFrame, Va1]);
      for i := parentLevel - 1 downto 0 do
      begin
        Va1 := TempVar;
        parentCntx := TEmitFuncContext(FCntxList[i + 1]);
        WriteCode('%s = getelementptr %s, %s* %%.fp%d, %%SizeInt 0, %%SizeInt %d',
          [Va1, parentCntx.FrameTyStr, i + 1, parentCntx.LinkedFrameIndex]);
        parentCntx := TEmitFuncContext(FCntxList[i]);
        WriteCode('%%.fp%d = load %s, %s %s', [i, parentCntx.FrameTyStr.Replace('*', '') +
          StringOfChar('*', parentCntx.FrameTyStr.CountChar('*') - 1), parentCntx.FrameTyStr, Va1]);
      end;
      parentCntx := TEmitFuncContext(FCntxList[0]);
      if Assigned(parentCntx.SelfVar) then
      begin
        Va1 := TempVar;
        WriteCode('%s = getelementptr %s, %s* %%.fp0, %%SizeInt 0, %%SizeInt %d',
          [Va1, parentCntx.FrameTyStr, parentCntx.FrameTyStr, parentCntx.SelfVar.Index]);
        WriteCode('%Self = load i8*, i8** ' + Va1);
      end;
    end;
    List := TCode(Func.Codes).Vars;
    for i := 0 to
      List.Count - 1 do
    begin
      Sym := TSymbol(List[i]);
      case Sym.NodeKind of
        nkVariable: VarInit(TVariable(Sym));
        nkFuncParam: ArgInit(TFuncParam(Sym));
      end;
    end;
  end;

  procedure CheckLocal(Func: TFunction);
  var
    i: integer;
    Sym: TSymbol;
    Arg: TFuncParam;
    V: TVariable;
    List: TFPList;
    NestRef, HasAutoFreeVar: boolean;
  begin
    HasAutoFreeVar := False;
    List := TCode(Func.Codes).Vars;
    NestRef := TCode(Func.Codes).Funcs.Count > 0;
    for i := 0 to List.Count - 1 do
    begin
      Sym := TSymbol(List[i]);
      if not (saUsed in Sym.Attr) then
        Continue;
      case Sym.NodeKind of
        nkVariable: if vaLocal in TVariable(Sym).VarAttr then
          begin
            V := TVariable(Sym);
            if vaResult in V.VarAttr then
            begin
              if FCurCntx.RetConverted then
                Include(V.States, vsResultAddr);
              FCurCntx.ResultVar := V;
            end
            else if vaSelf in V.VarAttr then
            begin
              FCurCntx.SelfVar := V;
            end
            else
            begin
              if NeedInit(V.VarType) then
                Include(V.States, vsNeedInit);
              if NeedFree(V.VarType) then
                Include(V.States, vsNeedFree);
              if (vsNeedInit in V.States) or (vsNeedFree in V.States) then
                Include(V.States, vsNestRef);
            end;
            if vsNestRef in V.States then
              NestRef := True;
            if not HasAutoFreeVar then
              HasAutoFreeVar := vsNeedFree in V.States;
          end;
        nkFuncParam:
        begin
          Arg := TFuncParam(Sym);
          if Arg.Modifier in [argOut, argVar] then
            Include(Arg.States, asByRef);
          if (Arg.Modifier = argConst) then
          begin
            if (Arg.ParamType.TypeCode = typUntype) then
              Include(Arg.States, asByRef)
            else if IsStructType(Arg.ParamType) then
            begin
              Include(Arg.States, asByRef);
              Include(Arg.States, asStructRef);
            end;
          end;
          if (Arg.Modifier = argDefault) then
          begin
            if IsStructType(Arg.ParamType) then
              Include(Arg.States, asStructValue);
            if NeedInit(Arg.ParamType) then
              Include(Arg.States, asNeedAddRef);
            if NeedFree(Arg.ParamType) then
            begin
              Include(Arg.States, asNeedFree);
              Include(Arg.States, asNestRef);
            end;
          end;
          if asNestRef in Arg.States then
            NestRef := True;
          if not HasAutoFreeVar then
            HasAutoFreeVar := asNeedFree in Arg.States;
        end;
      end;
    end;
    FCurCntx.NeedFrame := NestRef or (FCurCntx.Level > 0);
    FCurCntx.HasAutoFreeVar := HasAutoFreeVar;
  end;

  procedure SetupLocal(Func: TFunction);
  var
    i: integer;
    fpIndex: word;
    fpAlign, typAlign: byte;
    fpSize: cardinal;
    offset: cardinal;
    sf: string;
    Sym: TSymbol;
    Arg: TFuncParam;
    V: TVariable;

    procedure AdjustAlign(T: TType);
    begin
      typAlign := T.AlignSize;
      if typAlign > fpAlign then
        fpAlign := typAlign;
      if typAlign > 1 then
      begin
        offset := (offset + typAlign - 1) and not (typAlign - 1);
        if offset > fpSize then
        begin
          sf := sf + Format('[%d x i8], ', [offset - fpSize]);
          Inc(fpIndex);
        end;
      end;
      Inc(offset, T.Size);
      fpSize := offset;
    end;

  var
    List: TFPList;
  begin
    fpIndex := 0;
    fpSize := 0;
    fpAlign := 0;
    offset := 0;
    List := TCode(Func.Codes).Vars;
    for i := 0 to List.Count - 1 do
    begin
      Sym := TSymbol(List[i]);
      if not (saUsed in Sym.Attr) then
        Continue;
      case Sym.NodeKind of
        nkVariable: if vsNestRef in TVariable(Sym).States then
          begin
            V := TVariable(Sym);
            adjustAlign(V.VarType);
            V.Index := fpIndex;
            Inc(fpIndex);
            if vsResultAddr in V.States then
              sf := sf + TypeStr(V.VarType) + '*, '
            else
              sf := sf + TypeStr(V.VarType) + ', ';
          end;
        nkFuncParam: if asNestRef in TFuncParam(Sym).States then
          begin
            Arg := TFuncParam(Sym);
            adjustAlign(Arg.ParamType);
            Arg.Index := fpIndex;
            Inc(fpIndex);
            if (Arg.ParamType.TypeCode = typOpenArray) then
              Inc(fpIndex);
            if asByRef in Arg.States then
              sf := sf + TypeStr(Arg.ParamType) + '*, '
            else
              sf := sf + TypeStr(Arg.ParamType) + ', ';
            if (Arg.ParamType.TypeCode = typOpenArray) then
              sf := sf + '%%SizeInt, ';
          end;
      end;
    end;
    if FCurCntx.Level > 0 then
    begin
      Assert(FCurCntx.Func.Parent.NodeKind in [nkFunc, nkMethod]);
      sf := sf + Format('%s*, ', [TEmitFuncContext(FCntxList[FCurCntx.Level - 1]).FrameTyStr]);
      if fpAlign < FModule.PointerSize then
        fpAlign := FModule.PointerSize;
    end
    else if FCurCntx.NeedFrame and (sf = '') then
    begin
      sf := sf + '%%SizeInt, ';
      fpAlign := SizeOf(Pointer);
    end;
    if sf <> '' then
    begin
      Delete(sf, Length(sf) - 1, 2);
      FCurCntx.FrameDecl := Format('%%%s.$frame = type <{%s}>', [FCurCntx.MangledName, sf]);
      FCurCntx.FrameTyStr := Format('%%%s.$frame', [FCurCntx.MangledName]);
      FCurCntx.FrameAlign := fpAlign;
    end;
  end;

  procedure WriteFrameDecl;
  begin
    WriteDecl(FCurCntx.FrameDecl);
    WriteCode('%%.fp = alloca %%%s.$frame, align %d', [MangledName(Func), FCurCntx.FrameAlign]);
    //WriteCode('%%.fp = alloca %%%s.$frame', [MangledName(Func)]);
  end;

  procedure WriteRet;
  var
    s, TempTyStr: string;
    V: TVariable;
  begin
    V := FCurCntx.ResultVar;
    if FCurCntx.IsSafecall then
      WriteCode('ret i32 0')
    else
    if (V = nil) or FCurCntx.RetConverted then
      WriteCode('ret void')
    else
    begin
      s := TempVar;
      TempTyStr := TypeStr(V.VarType) + '*';
      WriteCode('%s = load %s, %s %%Result.addr', [s, TempTyStr.Replace('*', '') + StringOfChar(
        '*', TempTyStr.CountChar('*') - 1), TempTyStr]);
      WriteCode('ret %s %s', [TypeStr(V.VarType), s]);
    end;
  end;

  procedure WriteNested(F: TFunction);
  var
    i: integer;
    Funcs: TFPList;
  begin
    Funcs := TCode(F.Codes).Funcs;
    for i := 0 to Funcs.Count - 1 do
      EmitFunc(TFunction(Funcs[i]));
    if TCode(F.Codes).VarCleanFunc <> nil then
      EmitFunc(TCode(F.Codes).VarCleanFunc);
  end;

  procedure InsertCodes;
  var
    i: integer;
  begin
    for i := 0 to FCurCntx.Codes.Count - 1 do
      WriteCodeNI(FCurCntx.Codes[i]);
  end;

  procedure WriteCtorEnter;
  var
    Va1, FunTy: string;
  begin
    WriteCode('br label %ctor.entry');
    WriteLabel('ctor.entry');
    Va1 := TempVar;
    WriteCode('%s = icmp ugt i8 %%.flag, 0', [Va1]);
    WriteCode('br i1 %s, label %%ctor.alloc, label %%ctor.noalloc', [Va1]);
    WriteLabel('ctor.alloc');
    EmitLoadVmtCast('%.vmt', 'i8*', False, FNewInstanceFunc, Va1, FunTy);
    WriteCode('%%.ctor.inst = call %s i8* %s(i8* %%.vmt)', [CCStr(FNewInstanceFunc.CallConvention), Va1]);
    WriteCode('br label %ctor.noalloc');
    WriteLabel('ctor.noalloc');
    WriteCode('%Self = phi i8* [%.ctor.inst, %ctor.alloc], [%.vmt, %ctor.entry]');
  end;

  procedure WriteCtorAfter;
  var
    Va, FunPtr, FunTy, L1: string;
  begin
    WriteCode('store i8* %Self, i8** %Result.addr');
    Va := TempVar;
    WriteCode('%s = load i8*, i8** %%Result.addr', [Va]);
    EmitLoadVmtCast(Va, 'i8*', True, FAfterConstructionFunc, FunPtr, FunTy);
    L1 := Self.LabelStr;
    WriteCode('invoke %s void %s(i8* %s) to label %%%s unwind label %%ctor.lpad',
      [CCStr(FAfterConstructionFunc.CallConvention), FunPtr, Va, L1]);
    WriteLabel(L1);
  end;

  procedure WriteDtorEnter;
  var
    Va1, FunTy: string;
  begin
    Va1 := TempVar;
    WriteCode('%s = icmp ne i8 %%.outterMost, 0', [Va1]);
    WriteCode('br i1 %s, label %%dtor.outterMost, label %%dtor.inner', [Va1]);
    WriteLabel('dtor.outterMost');
    EmitLoadVmtCast('%Self', 'i8*', True, FBeforeDestructionFunc, Va1, FunTy);
    WriteCode('call %s void %s(i8* %%Self)', [CCStr(FBeforeDestructionFunc.CallConvention), Va1]);
    WriteCode('br label %dtor.inner');
    WriteLabel('dtor.inner');
  end;

  procedure WriteDtorExit;
  var
    Va, FunTy: string;
  begin
    Va := TempVar;
    WriteCode('%s = icmp ne i8 %%.outterMost, 0', [Va]);
    WriteCode('br i1 %s, label %%dtor.free, label %%dtor.quit', [Va]);
    WriteLabel('dtor.free');
    EmitLoadVmtCast('%Self', 'i8*', True, FFreeInstanceFunc, Va, FunTy);
    WriteCode('call %s void %s(i8* %%Self)', [CCStr(FFreeInstanceFunc.CallConvention), Va]);
    WriteCode('br label %dtor.quit');
    WriteLabel('dtor.quit');
  end;

  procedure WriteCtorLPad(const LPad: string);
  var
    Va1, Va2: string;
  begin
    LeaveLandingPad;
    WriteLabel(LPad);
    Va1 := TempVar;
    WriteCode(Va1 + ' = landingpad {i8*, i32}');
    WriteCode('   catch i8* bitcast(i8** @_ZTIPv to i8* )');
    WriteCode('%%.ctor.ex = extractvalue {i8*, i32} %s, 0', [Va1]);
    WriteCode('store i8* %.ctor.ex, i8** %$exptr.addr');
    WriteCode('br label %' + LPad + '.body');
    WriteLabel(LPad + '.body');
    Va2 := TempVar;
    WriteCode('%s = load i8*, i8** %%$exptr.addr', [Va2]);
    EmitCallSys(srHandleCtorExcept, ['i8*', 'i8*', 'i8'], [Va2, '%Self', '%.flag']);
    WriteCode('unreachable');
  end;

  procedure WriteSafecallLPad(const LPad: string);
  var
    Va1, Va2, ThisPtr: string;
  begin
    LeaveLandingpad;
    WriteLabel('sc.lpad');
    Va1 := TempVar;
    WriteCode(Va1 + ' = landingpad {i8*, i32}');
    WriteCode('   catch i8* bitcast(i8** @_ZTIPv to i8* )');
    WriteCode('%%.sc.ex = extractvalue {i8*, i32} %s, 0', [Va1]);
    WriteCode('store i8* %.sc.ex, i8** %$exptr.addr');
    WriteCode('br label %' + LPad + '.body');
    WriteLabel(LPad + '.body');
    if FCurCntx.IsMeth then
      ThisPtr := '%Self'
    else
      ThisPtr := 'null';
    Va2 := TempVar;
    WriteCode('%s = load i8*, i8** %%$exptr.addr', [Va2]);
    Va1 := TempVar;
    EmitCallSys(srHandleSafeCallExcept, ['i8*', 'i8*'], [ThisPtr, Va2], Va1);
    WriteCode('ret i32 ' + Va1);
  end;

  procedure WriteLandingPad(const LPad: string; Handler: TFunction); overload;
  var
    va, va2: string;
  begin
    WriteLabel(LPad);
    Va2 := TempVar;
    WriteCode(Va2 + ' = landingpad { i8*, i32 }');
    WriteCode('   catch i8* bitcast(i8** @_ZTIPv to i8*)');
    Va := TempVar;
    WriteCode('%s = extractvalue { i8*, i32 } %s, 0', [Va, Va2]);
    WriteCode('store i8* %s, i8** %%$exptr.addr', [Va]);
    Va := TempVar;
    WriteCode('%s = extractvalue { i8*, i32 } %s, 1', [Va, Va2]);
    WriteCode('store i32 %s, i32* %%$exsel.addr', [Va]);
    WriteCode('br label %' + LPad + '.body');
    WriteLabel(LPad + '.body');
    EmitCall(Handler, [FCurCntx.FrameTyStr + '*'], ['%.fp'], '');
    if Self.CurLandingPad = '' then
    begin
      Va := TempVar;
      WriteCode('%s = load i8*, i8** %%$exptr.addr', [Va]);
      WriteCode('call fastcc void @System._Rethrow(i8* %s) noreturn', [Va]);
    end
    else
    begin
      WriteCode('br label %%%s.body', [CurLandingPad]);
    end;
    WriteCode('unreachable');
    AddSystemRoutine(srRethrow);
  end;

  procedure WriteLandingPad(const LPad: string; Handler: THandleExceptCmd); overload;
  var
    Va, Va1: string;
  begin
    WriteLabel(LPad);
    Va := TempVar;
    WriteCode(Va + ' = landingpad { i8*, i32 }');
    WriteCode('   catch i8* bitcast(i8** @_ZTIPv to i8*)');
    Va1 := TempVar;
    WriteCode('%s = extractvalue { i8*, i32 } %s, 0', [Va1, Va]);
    WriteCode('store i8* %s, i8** %%$exptr.addr', [Va1]);
    Va1 := TempVar;
    WriteCode('%s = extractvalue { i8*, i32 } %s, 1', [Va1, Va]);
    WriteCode('store i32 %s, i32* %%$exsel.addr', [Va1]);
    WriteCode('br label %%%s', [LPad + '.body']);
    WriteLabel(LPad + '.body');
    va := TempVar;
    WriteCode('%s = load i8*, i8** %%$exptr.addr', [va]);
    va1 := TempVar;
    WriteCode('%s = tail call i8* @__cxa_begin_catch(i8* %s) nounwind', [va1, va]);
    WriteCode('store i8* %s, i8** %%%s.addr', [va1, Handler.ExceptVar]);
    Self.EnterLandingpad(LPad + '.catch');
    EmitCmds(Handler.Cmds);
    Self.LeaveLandingpad;
    WriteCode('br label %%%s.quit', [LPad]);
    WriteLabel(Format('%s.quit', [LPad]));
    WriteCode('call fastcc void @System._FreeExceptObject(i8** %%%s.addr)', [Handler.ExceptVar]);
    WriteCode('tail call void @__cxa_end_catch()');
    WriteCode('br label %%%s.leave', [LPad]);
    WriteLabel(Format('%s.catch', [LPad]));
    va := TempVar;
    WriteCode(va + ' = landingpad { i8*, i32 }');
    WriteCode('   cleanup');
    va1 := TempVar;
    WriteCode('%s = extractvalue { i8*, i32 } %s, 0', [va1, va]);
    WriteCode('store i8* %s, i8** %%$exptr.addr', [va1]);
    Va1 := TempVar;
    WriteCode('%s = extractvalue { i8*, i32 } %s, 1', [Va1, Va]);
    WriteCode('store i32 %s, i32* %%$exsel.addr', [Va1]);
    WriteCode('br label %%%s.catch.body', [LPad]);
    WriteLabel(Format('%s.catch.body', [LPad]));
    WriteCode('invoke void @__cxa_end_catch() to label %%%s.resume unwind label %%lpad.terminate', [LPad]);
    WriteLabel(Format('%s.resume', [LPad]));
    WriteCode('call fastcc void @System._FreeExceptObject(i8** %%%s.addr)', [Handler.ExceptVar]);
    if Handler.OutterLPad <> '' then
      WriteCode('br label %' + Handler.OutterLPad + '.body')
    else
    begin
      va := TempVar;
      WriteCode('%s = load i8*, i8** %%$exptr.addr', [va]);
      WriteCode('call fastcc void @System._Rethrow(i8* %s) noreturn', [va]);
    end;
    WriteCode('unreachable');
    FCurCntx.TerminatedUsed := True;
    AddSystemRoutine(srTerminated);
    AddSystemRoutine(srFreeExceptObject);
    AddSystemRoutine(srRethrow);
  end;

  procedure WriteLandingPads;
  var
    i: integer;
    LCmd: TCmd;
    LPad: string;
  begin
    while FCurCntx.Landingpads.Count > 0 do
      for i := FCurCntx.Landingpads.Count - 1 downto 0 do
      begin
        LPad := FCurCntx.Landingpads[i];
        LCmd := TCmd(FCurCntx.Landingpads.Objects[i]);
        FCurCntx.Landingpads.Delete(i);
        if Assigned(LCmd) then
        begin
          case LCmd.Kind of
            insCleanup:
            begin
              if TCleanupCmd(LCmd).OutterLPad <> '' then
                EnterLandingpad(TCleanupCmd(LCmd).OutterLPad);
              WriteLandingPad(LPad, TCleanupCmd(LCmd).CleanupProc);
              if TCleanupCmd(LCmd).OutterLPad <> '' then
                LeaveLandingpad;
            end;
            insHandleExcept: WriteLandingPad(LPad, THandleExceptCmd(LCmd));
            insHandleScExcept: WriteSafecallLPad(LPad);
            insHandleCtorExcept: WriteCtorLPad(LPad);
          end;
        end;
      end;
  end;

  procedure WriteCommonCodes;
  var
    va: string;
  begin
    if FCurCntx.TerminatedUsed then
    begin
      WriteLabel('lpad.terminate');
      va := TempVar;
      WriteCode(va + ' = landingpad { i8*, i32 }');
      WriteCode('    catch i8* null');
      WriteCode('tail call fastcc void @System._Terminated() noreturn nounwind');
      WriteCode('unreachable');
    end;
    if FCurCntx.UnreachableUsed then
    begin
      WriteLabel('lpad.unreachable');
      WriteCode('unreachable');
    end;
  end;

var
  OldCntx: TEmitFuncContext;
  OldCodes: TStringList;
  LinkAttr: string;
begin
  if Func.NodeKind = nkExternalFunc then
  begin
    if TExternalFunction(Func).FileName <> '' then
    begin
      Assert(TExternalFunction(Func).RoutineName <> '', 'emitFunc');
      WriteCodeNI('declare dllimport ' + FuncDecl(Func, False, TExternalFunction(Func).RoutineName));
    end
    else if TExternalFunction(Func).RoutineName <> '' then
    begin
      {if (FCurCntx.LandingPads <> nil) and (FCurCntx.LandingPads.Count > 0) then
        WriteCodeNI('declare ' + FuncDecl(Func, False, TExternalFunction(Func).RoutineName) + ' personality i8* bitcast (i32 (...)* @__CxxFrameHandler3 to i8*)')
      else}
      WriteCodeNI('declare ' + FuncDecl(Func, False, TExternalFunction(Func).RoutineName));
    end{
    else
    begin
      if (FCurCntx.LandingPads <> nil) and (FCurCntx.LandingPads.Count > 0) then
        WriteCodeNI('declare ' + FuncDecl(Func, False) + ' personality i8* bitcast (i32 (...)* @__CxxFrameHandler3 to i8*)')
      else
        WriteCodeNI('declare ' + FuncDecl(Func, False));
    end};
    WriteCodeNI('');
    Exit;
  end;
  OldCntx := FCurCntx;
  FCurCntx := TEmitFuncContext.Create;
  try
    if FTopCntx = nil then
      FTopCntx := FCurCntx;
    FCntxList.Add(FCurCntx);
    FCurCntx.Func := TFunction(Func);
    FCurCntx.Level := TFunction(Func).Level;
    FCurCntx.MangledName := MangledName(Func);
    FCurCntx.IsMeth := (Func.NodeKind = nkMethod) and not (saStatic in Func.Attr);
    FCurCntx.IsCtor := (Func.NodeKind = nkMethod) and (TMethod(Func).MethodKind = mkConstructor);
    FCurCntx.IsDtor := (Func.NodeKind = nkMethod) and (TMethod(Func).MethodKind = mkDestructor);
    FCurCntx.IsSafecall := Func.CallConvention = ccSafecall;
    FCurCntx.RetConverted := not FCurCntx.IsCtor and not FCurCntx.IsDtor and Assigned(Func.ReturnType) and
      (IsSpecialType(Func.ReturnType) or (FCurCntx.IsSafecall));
    FCurCntx.IsStaticFunc := (saStatic in Func.Attr);
    FCurCntx.IsClassFunc := (saClass in Func.Attr) and not (saStatic in Func.Attr);
    CheckLocal(FCurCntx.Func);
    SetupLocal(TFunction(Func));
    OldCodes := Self.FCodes;
    Self.FCodes := FCurCntx.Codes;
    try
      EmitCmds(TCode(TFunction(Func).Codes).Cmds);
    finally
      Self.FCodes := OldCodes;
    end;
    if saInternal in Func.Attr then
      LinkAttr := 'internal ';
    WriteCodeNI('define ' + LinkAttr + FuncDecl(Func, True));
    WriteCodeNI('{');
    if FCurCntx.NeedFrame then
      WriteFrameDecl;
    {if FCurCntx.IsCtor then
      WriteCtorEnter
    else if FCurCntx.IsDtor then
      WriteDtorEnter;}
    WriteLocalInit(TFunction(Func));
    InsertCodes;
    {if FCurCntx.IsCtor then
      WriteCtorAfter
    else if FCurCntx.IsDtor then
      WriteDtorExit;}
    WriteRet;
    {WriteLandingPads;}
    WriteCommonCodes;
    WriteCodeNI('}');
    WriteCodeNI('');
    WriteNested(TFunction(Func));
  finally
    FCurCntx.Free;
    FCurCntx := OldCntx;
    if FCurCntx = nil then
      FTopCntx := nil;
    if FCntxList.Count > 0 then
      FCntxList.Delete(FCntxList.Count - 1);
  end;
end;

procedure TCodeGen.EmitFuncCall(Left, Right: TBaseOp; Fun: TFunctionDecl; FunT: TProceduralType; var Result: TVarInfo);
var
  Count, I: integer;
  LV, ArgV: TVarInfo;
  ArgE, retE: TBaseOp;
  Arg: TFuncParam;
  RetVar, RetStr, RetTyStr, ArgStr, FunName, SelfPtr, Va1, Va2, lpad, nextLabel: string;
  ParentT: TType;
  IsMeth, IsVirtual, IsSafecall, IsTypePrefix, IsClassRefPrefix, IsClassRefVarPrefix, IsCallBase,
  IsCtorInner, IsDtorInner, IsNested, IsCtor, IsDtor, RetConv: boolean;
  CC: TCallingConvention;
  parentCntx: TEmitFuncContext;
begin
  Count := FunT.ParamCount;
  IsMeth := FunT.IsMethodPointer;
  IsSafecall := FunT.CallConvention = ccSafeCall;
  RetConv := Assigned(FunT.ReturnType) and (IsSpecialType(FunT.ReturnType) or IsSafecall);
  IsCallBase := oprInherited in Left.Parent.Attr;
  IsCtorInner := oprCtorInner in Left.Parent.Attr;
  IsDtorInner := oprDtorInner in Left.Parent.Attr;
  IsTypePrefix := (Left.OpCode = opcMember) and (TBinaryOp(Left).Left.IsTypeSymbol);
  IsClassRefPrefix := (Left.OpCode = opcMember) and (TBinaryOp(Left).Left.Typ.TypeCode = typClassRef);
  IsClassRefVarPrefix := IsClassRefPrefix and not IsTypePrefix;
  if Assigned(Fun) then
  begin
    IsNested := Fun.Level > 0;
    IsVirtual := (Fun.NodeKind = nkMethod) and (fmVirtual in Fun.Modifiers);
    IsCtor := (Fun.NodeKind = nkMethod) and (TMethod(Fun).MethodKind = mkConstructor);
    IsDtor := (Fun.NodeKind = nkMethod) and (TMethod(Fun).MethodKind = mkDestructor);
  end
  else
  begin
    IsNested := False;
    IsVirtual := False;
    IsCtor := False;
    IsDtor := False;
  end;
  VarInfoInit(LV);
  if Fun <> nil then
  begin
    if (Fun.NodeKind = nkExternalFunc) and (TExternalFunction(Fun).RoutineName <> '') then
      FunName := '@' + TExternalFunction(Fun).RoutineName
    else
      FunName := '@' + MangledName(Fun);
    if IsMeth then
    begin
      Assert(Fun.Parent.NodeKind = nkType, 'Method parent err');
      ParentT := TType(Fun.Parent);
      if Left.OpCode = opcSYMBOL then
      begin
        LV.Name := '%Self';
        LV.TyStr := 'i8*';
        LV.States := [];
      end
      else
      if Left.OpCode = opcMEMBER then
      begin
        EmitOp(TBinaryOp(Left).Left, LV);
        if ParentT.TypeCode in [typInterface, typClass] then
          EmitOp_VarLoad(LV);
        EnsurePtr(LV.TyStr, 'Instance of method is not ptr');
      end
      else
        Assert(False, 'EmitFuncCall, invalid left node');
      if (ParentT.TypeCode = typClass) and (saClass in Fun.Attr) and not IsTypePrefix and not
        IsClassRefVarPrefix and not FTopCntx.IsClassFunc then
      begin
        if LV.TyStr <> 'i8**' then
        begin
          Va1 := TempVar;
          WriteCode('%s = bitcast %s %s to i8**', [Va1, LV.TyStr, LV.Name]);
        end
        else
          Va1 := LV.Name;
        Va2 := TempVar;
        WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
        LV.Name := Va2;
        LV.TyStr := 'i8*';
        LV.States := [];
      end;
      if (IsVirtual or (ParentT.TypeCode = typInterface)) and not IsCallBase and not IsTypePrefix then
      begin
        if not (saClass in Fun.Attr) then
        begin
          if LV.TyStr <> 'i8***' then
          begin
            Va1 := TempVar;
            WriteCode('%s = bitcast %s %s to i8***', [Va1, LV.TyStr, LV.Name]);
          end
          else
            Va1 := LV.Name;
          if parentT.TypeCode = typObject then
          begin
            Va2 := TempVar;
            WriteCode('%s = getelementptr i8**, i8*** %s, %%SizeInt %d',
              [Va2, Va1, TObjectType(parentT).VmtOffset div FModule.PointerSize]);
            Va1 := Va2;
          end;
          Va2 := TempVar;
          WriteCode('%s = load i8**, i8*** %s', [Va2, Va1]);
        end
        else
        begin
          Va2 := TempVar;
          WriteCode('%s = bitcast %s %s to i8**', [Va2, LV.TyStr, LV.Name]);
        end;
        Va1 := TempVar;
        WriteCode('%s = getelementptr i8*, i8** %s, %%SizeInt %d', [Va1, Va2, TMethod(Fun).VTIndex]);
        Va2 := TempVar;
        WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
        Va1 := TempVar;
        WriteCode('%s = bitcast i8* %s to %s', [Va1, Va2, Self.ProcTypeStr(FunT)]);
        FunName := Va1;
      end;
      if LV.TyStr <> 'i8*' then
      begin
        Va1 := TempVar;
        WriteCode('%s = bitcast %s %s to i8*', [Va1, LV.TyStr, LV.Name]);
        SelfPtr := Va1;
      end
      else
        SelfPtr := LV.Name;
    end;
  end
  else
  begin
    EmitOp(Left, LV);
    if FunT.IsMethodPointer then
    begin
      Va1 := TempVar;
      WriteCode('%s = getelementptr [2 x i8*], [2 x i8*]* %s, i32 0, i32 1', [Va1, LV.Name]);
      Va2 := TempVar;
      WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
      SelfPtr := Va2;
      Va1 := TempVar;
      WriteCode('%s = getelementptr [2 x i8*], [2 x i8*]* %s, i32 0, i32 0', [Va1, LV.Name]);
      Va2 := TempVar;
      WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
      LV.Name := TempVar;
      LV.TyStr := Self.ProcTypeStr(FunT);
      WriteCode('%s = bitcast i8* %s to %s', [LV.Name, Va2, LV.TyStr]);
      FunName := LV.Name;
    end
    else
    begin
      EmitOp_VarLoad(LV);
      FunName := LV.Name;
    end;
  end;
  ArgStr := '';
  if IsMeth then
    Inc(Count);
  if RetConv then
    Inc(Count);
  if IsNested then
    Inc(Count);
  if IsCtor then
    Inc(Count);
  if IsDtor then
    Inc(Count);
  if Count > 0 then
  begin
    if IsMeth then
    begin
      ArgStr := Format('i8* %s, ', [SelfPtr]);
    end;
    if IsCtor then
    begin
      if IsCallBase or IsCtorInner then
        ArgStr := ArgStr + 'i8 0, '
      else
      if not IsTypePrefix and not IsClassRefPrefix then
        ArgStr := ArgStr + 'i8 -1, '
      else
        ArgStr := ArgStr + 'i8 1, ';
    end;
    if IsDtor then
    begin
      if IsCallBase or IsDtorInner then
        ArgStr := ArgStr + 'i8 0, '
      else
        ArgStr := ArgStr + 'i8 1, ';
    end;
    if IsNested then
    begin
      VarInfoInit(ArgV);
      parentCntx := TEmitFuncContext(FCntxList[Fun.Level - 1]);
      if parentCntx.Level = FCurCntx.Level then
        ArgStr := ArgStr + Format('%s* %%.fp, ', [parentCntx.FrameTyStr])
      else
        ArgStr := ArgStr + Format('%s* %%.fp%d, ', [parentCntx.FrameTyStr, parentCntx.Level]);
    end;
    if RetConv then
      with TListOp(Right) do
      begin
        RetE := Items[Count - 1];
        Delete(Count - 1);
      end
    else
      RetE := nil;
    for I := 0 to FunT.ParamCount - 1 do
    begin
      Arg := FunT.Params[I];
      if I < TListOp(Right).Count then
        ArgE := TListOp(Right).Items[I]
      else
        ArgE := nil;
      VarInfoInit(ArgV);
      if ArgE <> nil then
      begin
        EmitOp(ArgE, ArgV);
      end
      else
      begin
        Assert(Arg.DefaultValue.VT <> vtEmpty, 'EmitFuncCall');
        EmitOp_LoadConstValue(Arg.DefaultValue, Arg.ParamType, ArgV);
      end;
      if not (IsStructType(Arg.ParamType) or (Arg.Modifier in [argOut, argVar])) then
      begin
        EmitOp_VarLoad(ArgV);
      end;
      if (ArgE <> nil) then
      begin
        if (Arg.ParamType.TypeCode <> typUntype) then
          EmitCast(ArgV, ArgE.Typ, Arg.ParamType, Format('%s,%d,%d', [FunName, ArgE.Coord.Row, ArgE.Coord.Col]))
        else
        begin
          if not (vasAddrOfVar in ArgV.States) then
            EmitError('Var/Out/Const Argument expect variable');
          Va1 := Self.TempVar;
          WriteCode('%s = bitcast %s %s to i8*', [Va1, ArgV.TyStr, ArgV.Name]);
          ArgV.TyStr := 'i8*';
          ArgV.Name := Va1;
        end;
      end;
      ArgStr := ArgStr + Format('%s %s, ', [ArgV.TyStr, ArgV.Name]);
    end;
    if RetConv then
    begin
      Assert(Result.Name = '');
      EmitOp(RetE, Result);
      ArgStr := ArgStr + Format('%s %s, ', [Result.TyStr, Result.Name]);
    end;
  end;
  if ArgStr <> '' then
    Delete(ArgStr, Length(ArgStr) - 1, 2);
  if IsSafecall then
  begin
    RetVar := TempVar;
    RetStr := RetVar + ' = ';
    RetTyStr := 'i32';
  end
  else if Assigned(FunT.ReturnType) and not RetConv then
  begin
    VarInfoInit(Result);
    Result.Name := TempVar;
    Result.TyStr := TypeStr(FunT.ReturnType);
    RetVar := Result.Name;
    RetStr := Result.Name + ' = ';
    RetTyStr := Result.TyStr;
  end
  else
  begin
    RetVar := '';
    RetStr := '';
    RetTyStr := 'void';
  end;
  if IsSafecall then
    CC := ccStdCall
  else
    CC := FunT.CallConvention;
  if (Fun <> nil) and (fmVarargs in Fun.Modifiers) then
  begin
    RetTyStr := StringReplace(FuncDecl(Fun, False, '$$$$'), '@$$$$', '', []);
    RetTyStr := StringReplace(RetTyStr, CCStr(CC), '', []);
    RetTyStr := RetTyStr + '*';
  end;
  if IsCtor or IsDtor then
    WriteCode(';; IsTypePrefix=%s,IsClassrefPrefix=%s,IsCtorInner=%s,IsDtorInner=%s',
      [BoolStr[IsTypePrefix], BoolStr[IsClassrefPrefix], BoolStr[IsCtorInner], BoolStr[IsDtorInner]]);
  lpad := Self.CurLandingPad;
  if lpad = '' then
  begin
    WriteCode('%scall %s %s %s(%s)', [RetStr, CCStr(CC), RetTyStr.Replace(')*', ')'), FunName, ArgStr]);
  end
  else
  begin
    nextLabel := Self.LabelStr('next.');
    WriteCode('%sinvoke %s %s %s(%s) to label %%%s unwind label %%%s', [RetStr, CCStr(CC),
      RetTyStr, FunName, ArgStr, nextLabel, lpad]);
    WriteLabel(nextLabel);
  end;
  if IsSafecall then
    EmitCallSys(srSafecallCheck, [RetTyStr], [RetVar]);
  Self.AddExternalSymbol(Fun);
end;

procedure TCodeGen.EmitGlobalConstDecl(C: TConstant);

  procedure EmitAStrVar;
  var
    s: string;
  begin
    assert(C.Value.VT <> vtEmpty);
    s := MangledName(C);
    EmitStrA(False,
      s, ValToRawStr(C.Value), True);
  end;

  procedure EmitWStrVar;
  var
    s: string;
  begin
    s := MangledName(C);
    EmitStrW(False, s, ValToWStr(C.Value), True);
  end;

  procedure EmitUStrVar;
  var
    s: string;
  begin
    s := MangledName(C);
    EmitStrU(False, s, ValToWStr(C.Value), True);
  end;

  procedure EmitSStrVar;
  var
    s, s2: string;
    chCount: integer;
  begin
    s := MangledName(C);
    chCount := TStringType(C.ConstType).CharCount;
    s2 := ValToRawStr(C.Value);
    if Length(s2) > chCount then
      s2 := Copy(s2, 1, chCount)
    else if Length(s2) < chCount then
      s2 := s2 + StringOfChar(#0, chCount - Length(s2));
    s2 := Chr(byte(Length(s2))) + s2;
    EmitStrPa(False, s, s2, True);
  end;

  procedure EmitSWStrVar;
  var
    s: string;
    s2: WideString;
    chCount: integer;
  begin
    s := MangledName(C);
    chCount := TStringType(C.ConstType).CharCount;
    s2 := ValToWStr(C.Value);
    if Length(s2) > chCount then
      s2 := Copy(s2, 1, chCount)
    else if Length(s2) < chCount then
      s2 := s2 + StringOfChar(#0, chCount - Length(s2));
    s2 := widechar(word(Length(s2))) + s2;
    EmitStrPw(False, s, s2, True);
  end;

  procedure EmitPAStr;
  var
    s, s2: string;
  begin
    s := MangledName(C);
    s2 := ValToRawStr(C.Value);
    EmitStrPa(False, s, s2, True);
  end;

  procedure EmitPWStr;
  var
    s: string;
    s2: WideString;
  begin
    s := MangledName(C);
    s2 := ValToWStr(C.Value);
    EmitStrPw(False, s, s2, True);
  end;

begin
  case C.ConstType.TypeCode of
    typString: case TStringType(C.ConstType).Kind of
        strAnsi: EmitAStrVar;
        strWide: EmitWStrVar;
        strUnicode: EmitUStrVar;
        strAShort: EmitSStrVar;
        strWShort: EmitSWStrVar;
        else
          Assert(False, 'EmitGlobalConstDecl');
      end;
    typPWideChar: EmitPWStr;
    typPAnsiChar:
      EmitPAStr;
    typSet: Assert(False, 'todo');
  end;
end;

procedure TCodeGen.EmitGlobalVarDecl(V: TVariable);

  function InitValue: string;
  begin
    case V.Value.VT of
      vtEmpty: Result := 'zeroinitializer';
      vtInt: Result := IntToStr(V.Value.VInt);
      vtInt64: Result := IntToStr(V.Value.VInt64);
      vtReal: Result := FloatToStr(V.Value.VReal);
      vtCurr: Result := IntToStr(V.Value.VInt64);
      vtBool: Result := IntBoolStr[V.Value.VBool <> 0];
      vtAChr: Result := IntToStr(Ord(V.Value.VAChr));
      vtWChr: Result := IntToStr(word(V.Value.VWChr));
      else
        Result := 'zeroinitializer';
    end;
  end;

  procedure EmitAStrVar;
  var
    s: string;
    s2: UTF8String;
    pub: boolean;
  begin
    pub := not (saInternal in TSymbol(V).Attr);
    s := MangledName(V);
    if V.Value.VT = vtEmpty then
      WriteDecl(Format('@%s = %s global i8* null', [s, Visibility[pub]]))
    else
    begin
      s2 := ValToRawStr(V.Value);
      EmitStrA(pub, s + '.data', s2);
      WriteDecl(Format(
        '@%s = %s global i8* getelementptr({%%SizeInt, %%SizeInt, [%d x i8]}, {%%SizeInt, %%SizeInt, [%d x i8]}* @%s, %%SizeInt 0, %%SizeInt 2, %%SizeInt 0)',
        [s, Visibility[pub], Length(s2) + 1, Length(s2) + 1, s + '.data']));
    end;
  end;

  procedure EmitWStrVar;
  var
    s: string;
    s2: WideString;
    pub: boolean;
  begin
    pub := not (saInternal in TSymbol(V).Attr);
    s := MangledName(V);
    WriteDecl(Format('@%s = %s global i8* null', [s, Visibility[pub]]));
    if V.Value.VT <> vtEmpty then
    begin
      s2 := ValToWStr(V.Value);
      EmitStrW(pub, s + '.data', s2);
      AddInitWStr('@' + s, s + '.data', Format('{%%SizeInt, %%SizeInt, [%d x i16]}', [Length(s2) + 1]));
    end;
  end;

  procedure EmitUStrVar;
  var
    s: string;
    s2: WideString;
    pub: boolean;
  begin
    pub := not (saInternal in TSymbol(V).Attr);
    s := MangledName(V);
    if V.Value.VT = vtEmpty then
      WriteDecl(Format('@%s = %s global i6* null', [s, Visibility[pub]]))
    else
    begin
      s2 := ValToWStr(V.Value);
      EmitStrU(pub, s + '.data', s2);
      WriteDecl(Format(
        '@%s = %s global i16* getelementptr({%%SizeInt, %%SizeInt, [%d x i16]}, {%%SizeInt, %%SizeInt, [%d x i16]}* @%s, %%SizeInt 0, %%SizeInt 2, %%SizeInt 0)',
        [s, Visibility[pub], Length(s2) + 1, s + '.data']));
    end;
  end;

  procedure EmitSStrVar;
  var
    s, s2: string;
    chCount: integer;
    pub, isEmpty: boolean;
  begin
    s := MangledName(V);
    isEmpty := (V.Value.VT = vtEmpty) or (V.Value.VStr = nil);
    pub := not (saInternal in TSymbol(V).Attr);
    if isEmpty then
      s2 := 'zeroinitializer'
    else
    begin
      chCount := TStringType(V.VarType).CharCount;
      s2 := ValToRawStr(V.Value);
      if Length(s2) > chCount then
        s2 := Copy(s2, 1, chCount)
      else if Length(s2) < chCount then
        s2 := s2 + StringOfChar(#0, chCount - Length(s2));
      s2 := Chr(byte(Length(s2))) + s2;
      s2 := Format('c"%s"', [EncodeAStr(s2)]);
    end;
    WriteDecl(Format('@%s = %s unnamed_addr global [%d x i8] %s', [s, Visibility[pub],
      TStringType(V.VarType).CharCount + 1, s2]));
  end;

  function InitSetValue: string;
  var
    SetVal: TSetValue;
    i: integer;
  begin
    SetVal := ValToSet(V.Value);
    if (SetVal = nil) or (SetVal.IsEmpty) then
      Result := 'zeroinitializer'
    else
    begin
      Assert(TSetType(V.VarType).Size = 32);
      Result := '';
      for i := 0 to 31 do
        Result := Result + ', i8 ' + IntToStr(SetVal.Bits[i]);
      Delete(Result, 1, 1);
      Result := '[' + Result + ']';
    end;
  end;

var
  VisString, TlsString: String;

begin
  case V.VarType.TypeCode of
    typString: case TStringType(V.VarType).Kind of
        strAnsi: EmitAStrVar;
        strWide: EmitWStrVar;
        strUnicode: EmitUStrVar;
        strAShort: EmitSStrVar;
        else
          Assert(False);
      end;
    typSet: WriteDecl(Format('@%s = %s %s unnamed_addr constant %s %s', [MangledName(V),
        Visibility[saInternal in TSymbol(V).Attr], TlsStr[vaTls in V.VarAttr], TypeStr(V.VarType), InitSetValue]));
    else
    begin
      VisString := Visibility[saInternal in TSymbol(V).Attr];
      TlsString := TlsStr[vaTls in V.VarAttr];
      if (VisString <> '') and (TlsString <> '') then
        WriteDecl(Format('@%s = %s %s global %s %s', [MangledName(V), VisString, TlsString, TypeStr(V.VarType), InitValue]))
      else if (VisString = '') and (TlsString <> '') then
        WriteDecl(Format('@%s = %s global %s %s', [MangledName(V), TlsString, TypeStr(V.VarType), InitValue]))
      else if (VisString <> '') and (TlsString = '') then
        WriteDecl(Format('@%s = %s global %s %s', [MangledName(V), VisString, TypeStr(V.VarType), InitValue]))
      else
        WriteDecl(Format('@%s = global %s %s', [MangledName(V), TypeStr(V.VarType), InitValue]));
    end;
  end;
end;

procedure TCodeGen.EmitIns_Bit2Bol(var Result: TVarInfo);
var
  Va: string;
begin
  if Result.TyStr = 'i1' then
  begin
    Va := TempVar;
    WriteCode('%s = zext i1 %s to i8', [Va, Result.Name]);
    Result.Name := Va;
    Result.TyStr := 'i8';
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_Bitcast(var Result: TVarInfo; const desT: string);
var
  va: string;
begin
  if Result.TyStr <> desT then
  begin
    va := TempVar;
    WriteCode('%s = bitcast %s %s to %s', [va, Result.TyStr, Result.Name, desT]);
    Result.Name := va;
    Result.TyStr := desT;
  end;
end;

procedure TCodeGen.EmitIns_Bol2Bol(var Result: TVarInfo; typ: TType);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_Bol2Bol');
{$ENDIF}
  Va := TempVar;
  WriteCode('%s = icmp ne %s 0, %s', [Va, Result.TyStr, Result.Name]);
  Result.Name := TempVar;
  Result.TyStr := TypeStr(typ);
  WriteCode('%s = select i1 %s, %s -1, %s 0', [Result.Name, Va, Result.TyStr, Result.TyStr]);
  Result.States := [];
end;

procedure TCodeGen.EmitIns_Bol2I1(var Result: TVarInfo);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_Bol2I1');
{$ENDIF}
  if Result.TyStr <> 'i1' then
  begin
    Va := TempVar;
    WriteCode('%s = icmp ne %s 0, %s', [Va, Result.TyStr, Result.Name]);
    Result.Name := Va;
    Result.TyStr := 'i1';
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_Cur2Comp(var Result: TVarInfo);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, 'i64', 'EmitIns_Cur2Comp');
{$ENDIF}
  EmitIns_Cur2Flt(Result, 'double');
  Va := TempVar;
  WriteCode('%s = call @System._Round(double %s)', [Va, Result.Name]);
  Result.Name := Va;
  Result.TyStr := 'i64';
end;

procedure TCodeGen.EmitIns_Cur2Flt(var Result: TVarInfo; const desT: string);
var
  Va, Va2: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, 'i64', 'EmitIns_Cur2Flt');
  EnsureType(desT, llvmFloatTypeStrs, 'EmitIns_Cur2Flt');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    Va := TempVar;
    WriteCode('%s = sitofp i64 %s to %%LongDouble', [Va, Result.Name]);
    Va2 := TempVar;
    WriteCode('%s = fdiv double %s, 10000.0', [Va2, Va]);
    Result.Name := Va2;
    Result.TyStr := 'double';
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_Flt2Cur(var Result: TVarInfo);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmFloatTypeStrs, 'EmitIns_Flt2Cur');
{$ENDIF}
  if Result.TyStr = 'i64' then
  begin
    EmitIns_FltExt(Result, 'double');
    Va := TempVar;
    WriteCode('%s = fmul double %s, 10000.0', [Va, Result.Name]);
    Result.Name := Va;
    Va := TempVar;
    EmitCallSys(srRound, ['double'], [Result.Name], Va);
    Result.Name := Va;
    Result.TyStr := 'i64';
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_FltExt(var Result: TVarInfo; const desT: string);
var
  va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmFloatTypeStrs, 'EmitIns_FltExt');
  EnsureType(desT, llvmFloatTypeStrs, 'EmitIns_FltExt');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    va := TempVar;
    WriteCode('%s = fpext %s %s to %s', [va, Result.TyStr, Result.Name, desT]);
    Result.Name := va;
    Result.TyStr := desT;
  end;
end;

procedure TCodeGen.EmitIns_FltTrunc(var Result: TVarInfo; const desT: string);
var
  va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmFloatTypeStrs, 'EmitIns_FltTrunc');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    va := TempVar;
    WriteCode('%s = fptrunc %s %s to %s', [va, Result.TyStr, Result.Name, desT]);
    Result.Name := va;
    Result.TyStr := desT;
  end;
end;

procedure TCodeGen.EmitIns_Int2Bol(var Result: TVarInfo);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_Int2Bol');
{$ENDIF}
  Va := TempVar;
  WriteCode('%s = icmp ne %s 0, %s', [Va, Result.TyStr, Result.Name]);
  Result.Name := TempVar;
  Result.TyStr := 'i8';
  WriteCode('%s = select i1 %s, %s 1, %s 0', [Result.Name, Va, Result.TyStr, Result.TyStr]);
  Result.States := [];
end;

procedure TCodeGen.EmitIns_Int2Cur(var Result: TVarInfo; sign: boolean);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_Int2Cur');
{$ENDIF}
  EmitIns_IntExt(Result, 'i64', sign);
  Va := TempVar;
  WriteCode('%s = mul i64 %s, 10000', [Va, Result.Name]);
  Result.Name := Va;
  Result.TyStr := 'i64';
  Result.States := [];
end;

procedure TCodeGen.EmitIns_Int2Flt(var Result: TVarInfo; const desT: string; sign: boolean);
var
  va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_Int2Flt');
  EnsureType(desT, llvmFloatTypeStrs, 'EmitIns_Int2Flt');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    va := TempVar;
    if sign then
      WriteCode('%s = sitofp %s %s to %s', [va, Result.TyStr, Result.Name, desT])
    else
      WriteCode('%s = uitofp %s %s to %s', [va, Result.TyStr, Result.Name, desT]);
    Result.Name := va;
    Result.TyStr := desT;
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_Int2Ptr(var Result: TVarInfo; const desT: string);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_Int2Ptr');
  EnsurePtr(desT, 'EmitIns_Int2Ptr');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    Va :=
      TempVar;
    WriteCode('%s = inttoptr %s %s to %s', [Va, Result.TyStr, Result.Name, desT]);
    Result.Name := Va;
    Result.TyStr := desT;
    Result.States := [];
  end;
end;

procedure TCodeGen.
EmitIns_IntExt(var Result: TVarInfo; const desT: string; sign: boolean; const debugStr: string);
var
  va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_IntExt:' + Result.TyStr + ',' + debugStr);
  EnsureType(desT, llvmIntTypeStrs, 'EmitIns_IntExt:' + desT + ',' + debugStr);
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    va := TempVar;
    if Sign then
      WriteCode('%s = sext %s %s to %s', [va, Result.TyStr, Result.Name, desT])
    else
      WriteCode('%s = zext %s %s to %s', [va, Result.TyStr, Result.Name, desT]);
    Result.Name := va;
    Result.TyStr := desT;
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_IntTrunc(var Result: TVarInfo; const desT: string);
var
  va: string;
begin
{$IFDEF CHECKTYPE}
  EnsureType(Result.TyStr, llvmIntTypeStrs, 'EmitIns_IntTrunc');
  EnsureType(desT, llvmIntTypeStrs, 'EmitIns_IntTrunc');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    va := TempVar;
    WriteCode('%s = trunc %s %s to %s', [va, Result.TyStr, Result.Name, desT]);
    Result.Name := va;
    Result.TyStr := desT;
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIns_Memcpy(const desT, desN, srcT, srcN: string; len: int64; vol: boolean);
var
  s1, s2: string;
begin
  Include(FIntrinsics, llvm_memcpy);
  if desT <> 'i8*' then
  begin
    s1 := TempVar;
    WriteCode(Format('%s = bitcast %s %s to i8*', [s1, desT, desN]));
  end
  else
    s1 := desN;
  if srcT <> 'i8*' then
  begin
    s2 := TempVar;
    WriteCode(Format('%s = bitcast %s %s to i8*', [s2, srcT, srcN]));
  end
  else
    s2 := srcN;
  WriteCode(Format('call void @llvm.memcpy.p0i8.p0i8.i32(i8* %s, i8* %s, i32 %d, i32 1, i1 false)', [s1, s2, len]));
end;

procedure TCodeGen.EmitIns_Ptr2Int(var Result: TVarInfo; const desT: string);
var
  Va: string;
begin
{$IFDEF CHECKTYPE}
  EnsurePtr(Result.TyStr, 'EmitIns_Ptr2Int');
  EnsureType(desT, llvmIntTypeStrs, 'EmitIns_Ptr2Int');
{$ENDIF}
  if desT <> Result.TyStr then
  begin
    Va := TempVar;
    WriteCode('%s = ptrtoint %s %s to %s', [Va, Result.TyStr, Result.Name, desT]);
    Result.Name := Va;
    Result.TyStr := desT;
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitIntrinsics;
begin
  {WriteDecl('declare i32 @__gxx_personality_v0(...)');
  WriteDecl('declare i8* @__cxa_begin_catch(i8*)');
  WriteDecl('declare void @__cxa_end_catch()');
  WriteDecl('declare void @__cxa_rethrow()');
  WriteDecl('@_ZTIPv = external constant i8*');}
  if llvm_memcpy in FIntrinsics then
  begin
    WriteDecl('declare void @llvm.memcpy.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)');
    WriteDecl('declare void @llvm.memcpy.p0i8.p0i8.i64(i8*, i8*, i64, i32, i1)');
  end;
  if llvm_memmove in FIntrinsics then
  begin
    WriteDecl('declare void @llvm.memmove.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)');
    WriteDecl('declare void @llvm.memmove.p0i8.p0i8.i64(i8*, i8*, i64, i32, i1)');
  end;
  if llvm_rint in FIntrinsics then
  begin
    WriteDecl('declare float @llvm.rint.f32(float)');
    WriteDecl('declare double @llvm.rint.f64(double)');
  end;
  if llvm_ovfi8 in FIntrinsics then
  begin
    WriteDecl('declare {i8, i1} @llvm.sadd.with.overflow.i8(i8, i8)');
    WriteDecl('declare {i8, i1} @llvm.uadd.with.overflow.i8(i8, i8)');
    WriteDecl('declare {i8, i1} @llvm.ssub.with.overflow.i8(i8, i8)');
    WriteDecl('declare {i8, i1} @llvm.usub.with.overflow.i8(i8, i8)');
    WriteDecl('declare {i8, i1} @llvm.smul.with.overflow.i8(i8, i8)');
    WriteDecl('declare {i8, i1} @llvm.umul.with.overflow.i8(i8, i8)');
  end;
  if llvm_ovfi16 in FIntrinsics then
  begin
    WriteDecl('declare {i16, i1} @llvm.sadd.with.overflow.i16(i16, i16)');
    WriteDecl('declare {i16, i1} @llvm.uadd.with.overflow.i16(i16, i16)');
    WriteDecl('declare {i16, i1} @llvm.ssub.with.overflow.i16(i16, i16)');
    WriteDecl('declare {i16, i1} @llvm.usub.with.overflow.i16(i16, i16)');
    WriteDecl('declare {i16, i1} @llvm.smul.with.overflow.i16(i16, i16)');
    WriteDecl('declare {i16, i1} @llvm.umul.with.overflow.i16(i16, i16)');
  end;
  if llvm_ovfi32 in FIntrinsics then
  begin
    WriteDecl('declare {i32, i1} @llvm.sadd.with.overflow.i32(i32, i32)');
    WriteDecl('declare {i32, i1} @llvm.uadd.with.overflow.i32(i32, i32)');
    WriteDecl('declare {i32, i1} @llvm.ssub.with.overflow.i32(i32, i32)');
    WriteDecl('declare {i32, i1} @llvm.usub.with.overflow.i32(i32, i32)');
    WriteDecl('declare {i32, i1} @llvm.smul.with.overflow.i32(i32, i32)');
    WriteDecl('declare {i32, i1} @llvm.umul.with.overflow.i32(i32, i32)');
  end;
  if llvm_ovfi64 in FIntrinsics then
  begin
    WriteDecl('declare {i64, i1} @llvm.sadd.with.overflow.i64(i64, i64)');
    WriteDecl('declare {i64, i1} @llvm.uadd.with.overflow.i64(i64, i64)');
    WriteDecl('declare {i64, i1} @llvm.ssub.with.overflow.i64(i64, i64)');
    WriteDecl('declare {i64, i1} @llvm.usub.with.overflow.i64(i64, i64)');
    WriteDecl('declare {i64, i1} @llvm.smul.with.overflow.i64(i64, i64)');
    WriteDecl('declare {i64, i1} @llvm.umul.with.overflow.i64(i64, i64)');
  end;
  if llvm_malloc in FIntrinsics then
    WriteDecl('declare noalias i8* @malloc(i64) nounwind');
  if llvm_free in FIntrinsics then
    WriteDecl('declare void @free(i8* nocapture) nounwind');
end;

procedure TCodeGen.EmitLoadVmt(const VmtVar, VmtTy: string; IsInst: boolean; Offset: integer; out FunPtr: string);
var
  Va1, Va2: string;
begin
  if IsInst then
  begin
    if VmtTy <> 'i8***' then
    begin
      Va1 := TempVar;
      WriteCode('%s = bitcast %s %s to i8***', [Va1, VmtTy, VmtVar]);
    end
    else
      Va1 := VmtVar;
    Va2 := TempVar;
    WriteCode('%s = load i8**, i8*** %s', [Va2, Va1]);
  end
  else
  begin
    if VmtVar <> 'i8**' then
    begin
      Va2 := TempVar;
      WriteCode('%s = bitcast %s %s to i8**', [Va2, VmtTy, VmtVar]);
    end
    else
      Va2 := VmtVar;
  end;
  Va1 := TempVar;
  WriteCode('%s = getelementptr i8*, i8** %s, %%SizeInt %d', [Va1, Va2, Offset]);
  Va2 := TempVar;
  WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
  FunPtr := Va2;
end;

procedure TCodeGen.EmitLoadVmtCast(const VmtVar, VmtTy: string; IsInst: boolean; CastFunc: TMethod;
  out FunPtr, FunTy: string);
var
  Va: string;
begin
  EmitLoadVmt(VmtVar, VmtTy, IsInst, CastFunc.VTIndex, FunPtr);
  FunTy := Self.ProcTypeStr(CastFunc.ProceduralType);
  Va := TempVar;
  WriteCode('%s = bitcast %s %s to %s', [Va, 'i8*', FunPtr, FunTy]);
  FunPtr := Va;
end;

procedure TCodeGen.EmitModuleDecl(M: TModule);

  procedure EmitProgramEntry(M: TModule);
  begin
    Self.Emit(M.InitializeFunc);
    WriteCodeNI('define i32 @main(i32 %argc, i8** %argv)');
    WriteCodeNI('{');
    WriteCode('call %s void @%s()', [CCStr(M.InitializeFunc.CallConvention), MangledName(M.InitializeFunc)]);
    WriteCode('ret i32 0');
    WriteCodeNI('}');
  end;

  procedure EmitUnitEntry(M: TModule);
  begin
    if Assigned(M.InitializeFunc) then
      Emit(M.InitializeFunc);
    if Assigned(M.FinalizeFunc) then
      Emit(M.FinalizeFunc);
  end;

  procedure EmitLLVMDecl;
  var
    OldDecls: TStringList;
  begin
    OldDecls := FDecls;
    FDecls := FExtDecls;
    WriteDecl('; ModuleID = ''%s.pas''', [FModule.Name]);
    WriteDecl('source_filename = "%s.pas"', [FModule.Name]);
    {$ifdef CPU386}
    WriteDecl('target datalayout = "e-m:w-p:32:32-i64:64-f80:32-n8:16:32-S32"');
    {$else}
    WriteDecl('target datalayout = "e-m:w-i64:64-f80:128-n8:16:32:64-S128"');
    {$endif}
    WriteDecl('target triple = "%s"', [LLVMTarget]);
    WriteDecl('');
    FDecls := OldDecls;
  end;

  procedure EmitNativeType;
  var
    OldDecls: TStringList;
  begin
    OldDecls := FDecls;
    FDecls := FExtDecls;
    WriteDecl('%%NativeInt = type %s', [Self.NativeIntStr]);
    WriteDecl('%%SizeInt = type %s', [Self.NativeIntStr]);
    WriteDecl('%%LongDouble = type %s', [Self.LongDoubleStr]);
    FDecls := OldDecls;
  end;

  procedure EmitConsts;
  var
    i: integer;
    C: TConstant;
    V: TVariable;
  begin
    for i := 0 to FStrConstList.Count - 1 do
    begin
      C := TConstant(FStrConstList.Item[i]);
      Self.EmitGlobalConstDecl(C);
      C.Free;
    end;
    for i := 0 to FSetConstList.Count - 1 do
    begin
      V := TVariable(FSetConstList.Item[i]);
      Self.EmitGlobalVarDecl(V);
      V.Free;
    end;
  end;

  procedure LoadObjectMethods;

    function Get(const S: string): TMethod;
    var
      Sym: TSymbol;
    begin
      Sym := FContext.FTObjectType.FindSymbol(S);
      if not Assigned(Sym) then
        EmitError('TObject.%s not found', [S]);
      if (Sym.NodeKind <> nkMethod) or not (fmVirtual in TMethod(Sym).Modifiers) then
        EmitError('TObject.%s invalid', [S]);
      Result := TMethod(Sym);
    end;

  begin
    FNewInstanceFunc := Get('NewInstance');
    FAfterConstructionFunc := Get('AfterConstruction');
    FFreeInstanceFunc := Get('FreeInstance');
    FBeforeDestructionFunc := Get('BeforeDestruction');
  end;

var
  i: integer;
  Sym: TSymbol;
begin
  FModule := M;
  EmitLLVMDecl;
  EmitNativeType;
  LoadObjectMethods;
  if FModule.Name = 'System' then
    EmitSysTypeInfo;
  for i := 0 to FModule.Symbols.Count - 1 do
  begin
    Sym := FModule.Symbols[i];
    EmitSymbolDecl(Sym);
  end;
  for i := 0 to FModule.InternalSymbols.Count - 1 do
  begin
    Sym := FModule.InternalSymbols[i];
    EmitSymbolDecl(Sym);
  end;
  case M.Kind of
    mkProgram: EmitProgramEntry(M);
    mkUnit: EmitUnitEntry(M);
    else
      Assert(False, 'EmitModule');
  end;
  EmitIntrinsics;
  EmitExternals;
  EmitConsts;
end;

procedure TCodeGen.EmitOp(E: TBaseOp; var Result: TVarInfo);

  function BaseMapOf(T: TType): TBaseKind;
  begin
    if T = nil then
      Self.EmitError(E.Coord, 'BaseMapOf: T is null %d', [Ord(e.OpCode)]);
    case T.TypeCode of
      typInt: Result := IntBaseMaps[TIntType(T).Kind];
      typNumeric: Result := NumBaseMaps[TNumericType(T).Kind];
      typBool: Result := BoolBaseMaps[TBoolType(T).Kind];
      typChar: Result := CharBaseMaps[TCharType(T).Kind];
      typSubrange: Result := BaseMapOf(TSubrangeType(T).BaseType);
      typPointer, typPAnsiChar, typPWideChar, typProcedural, typClass, typClassRef, typInterface,
      typDynamicArray: Result := bkPtr;
      else
        Result := bkAny;
    end;
  end;

var
  lbt, rbt: TBaseKind;
begin
  case E.OpCode of
    opcNE..opcGE, opcADD..opcSHR:
    begin
      lbt := BaseMapOf(TBinaryOp(E).Left.Typ);
      rbt := BaseMapOf(TBinaryOp(E).Right.Typ);
      case SimpleOpMaps[lbt, rbt] of
        bkBol: EmitOp_Boolean(E, Result);
        bkInt: EmitOp_Int(E, Result);
        bkBig: EmitOp_Int64(E, Result);
        bkFlt: EmitOp_Float(E, Result);
        bkCur: EmitOp_Currency(E, Result);
        bkChr: EmitOp_Char(E, Result);
        bkPtr: EmitOp_Ptr(E, Result);
        else
          Assert(False);
      end;
    end;
    opcMEMBER: EmitOp_Member(TBinaryOp(E), Result);
    opcADDR: EmitOp_Addr(TUnaryOp(E), Result);
    opcINST: EmitOp_Inst(TUnaryOp(E), Result);
    opcCAST: EmitOp_Cast(TBinaryOp(E), Result);
    opcCALL, opcCallSpecial, opcCallBuiltin:
    begin
      if E.CmdCount > 0 then
        EmitCmdOfOp(E);
      EmitOp_Call(TBinaryOp(E), Result);
    end;
    opcINDEX: EmitOp_Index(TBinaryOp(E), Result);
    opcNOT: EmitOp_Not(TUnaryOp(E), Result);
    opcNEG: EmitOp_Neg(TUnaryOp(E), Result);
    opcSYMBOL:
    begin
      EmitCmdOfOp(E);
      EmitOp_Load(TSymbolOp(E), Result);
    end;
    opcNIL:
    begin
      Result.Name := 'null';
      Result.TyStr := 'i8*';
      Result.States := [vasAddrValue];
    end;
    opcCONST: EmitOp_LoadConst(TConstOp(E), Result);
    opcProcAddr: EmitOp_ProcAddr(TUnaryOp(E), Result);
    else
      Assert(False, 'EmitOp');
  end;
  if not (E.OpCode in [opcSYMBOL, opcCALL, opcCallSpecial]) and (E.CmdCount > 0) then
    Assert(False, 'EmitOp: no expected op has attached stmt');
end;

procedure TCodeGen.EmitOp_Addr(E: TUnaryOp; var Result: TVarInfo);
begin
  EmitOp(E.Operand, Result);
  if E.Operand.IsFunctionSymbol then
    Exit;
  Self.EmitIns_Bitcast(Result, TypeStr(E.Typ));
  if vasAddrOfVar in Result.States then
  begin
    Exclude(Result.States, vasAddrOfVar);
    Include(Result.States, vasAddrValue);
    Exit;
  end;
  Assert(False);
end;

procedure TCodeGen.EmitOp_Boolean(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  lbPre, lbLeft, lbRight, lbEnd, lbPhi1, lbPhi2, v, op: string;
begin
  L.States := [];
  R.States := [];
  if not (cdBoolEval in E.Switches) and (E.OpCode in [opcOR, opcAND]) then
  begin
    Inc(FExprID);
    lbPre := Format('expr%d.', [FExprID]);
    lbLeft := LabelStr(lbPre);
    lbRight := Self.LabelStr(lbPre);
    lbEnd := Self.LabelStr(lbPre);
    WriteCode('br label %%%s', [lbLeft]);
    WriteLabel(lbLeft);
    EmitOp(TBinaryOp(E).Left, L);
    EmitOp_VarLoad(L);
    EmitIns_Bol2I1(L);
    lbPhi1 := FCurLabel;
    if E.OpCode = opcAND then
      WriteCode('br i1 %s, label %%%s, label %%%s', [L.Name, lbRight, lbEnd])
    else
      WriteCode('br i1 %s, label %%%s, label %%%s', [L.Name, lbEnd, lbRight]);
    WriteLabel(lbRight);
    EmitOp(TBinaryOp(E).Right, R);
    EmitOp_VarLoad(R);
    EmitIns_Bol2I1(R);
    lbPhi2 := FCurLabel;
    WriteCode('br label %%%s', [lbEnd]);
    WriteLabel(lbEnd);
    v := TempVar;
    WriteCode('%s = phi i1 [ %s, %%%s], [ %s, %%%s ]', [v, L.Name, lbPhi1, R.Name, lbPhi2]);
    Result.Name := v;
    Result.TyStr := 'i1';
    Result.States := [];
  end
  else
  begin
    EmitOp(TBinaryOp(E).Left, L);
    EmitOp(TBinaryOp(E).Right, R);
    EmitOp_VarLoad(L);
    EmitIns_Bol2I1(L);
    EmitOp_VarLoad(R);
    EmitIns_Bol2I1(R);
    case E.OpCode of
      opcAND: op := 'and';
      opcOR: op := 'or';
      opcXOR: op := 'xor';
      else
        EmitError(E.Coord, 'EmitOp_boolean, Invalid Op');
    end;
    V := TempVar;
    WriteCode('%s = %s i1 %s, %s', [V, op, L.Name, R.Name]);
    Result.Name := V;
    Result.TyStr := 'i1';
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitOp_Call(E: TBinaryOp; var Result: TVarInfo);
var
  FunT: TProceduralType;
  Ref: TSymbol;
begin
  Ref := E.Left.GetReference;
  if (Ref <> nil) and (Ref.NodeKind = nkBuiltinFunc) then
  begin
    EmitBuiltin(E, TBuiltinFunction(Ref), TListOp(E.Right), Result);
  end
  else
  begin
    if (Ref <> nil) and (Ref.NodeKind in [nkMethod, nkFunc, nkExternalFunc]) then
      FunT := TFunctionDecl(Ref).ProceduralType
    else
    begin
      Assert(E.Left.Typ.TypeCode = typProcedural);
      Assert((Ref = nil) or (Ref.NodeKind = nkVariable));
      if Ref <> nil then
        Ref := nil;
      FunT := TProceduralType(E.Left.Typ);
    end;
    EmitFuncCall(E.Left, E.Right, TFunctionDecl(Ref), FunT, Result);
  end;
end;

procedure TCodeGen.EmitOp_Cast(E: TBinaryOp; var Result: TVarInfo);
var
  SrcE: TBaseOp;
  V: TVarInfo;
begin
  Assert(E.Right <> nil);
  SrcE := E.Right;
  Assert(SrcE <> nil);
  V.States := [];
  EmitOp(SrcE, V);
  if oprVarCast in E.Attr then
  begin
    Result.TyStr := TypeStr(E.Typ) + '*';
    if V.TyStr <> Result.TyStr then
    begin
      Result.Name := TempVar;
      WriteCode('%s = bitcast %s %s to %s', [Result.Name, V.TyStr, V.Name, Result.TyStr]);
    end
    else
      Result.Name := V.Name;
    Result.States := V.States;
  end
  else
  begin
    EmitOp_VarLoad(V, Result);
    EmitCast(Result, SrcE.Typ, E.Typ);
  end;
end;

procedure TCodeGen.EmitOp_Char(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  LT, RT: TType;
  ExtTy: string;
const
  CharOpMaps: array[opcNE..opcGE] of string = ('icmp ne', 'icmp eq', 'icmp ult', 'icmp ule', 'icmp ugt', 'icmp uge');
begin
  Assert(E.OpCode in [opcNE..opcGE]);
  L.States := [];
  R.States := [];
  EmitOp(TBinaryOp(E).Left, L);
  EmitOp(TBinaryOp(E).Right, R);
  LT := TBinaryOp(E).Left.Typ;
  RT := TBinaryOp(E).Right.Typ;
  if (LT.BaseCode = btcWideChar) or (RT.BaseCode = btcWideChar) then
    ExtTy := 'i16'
  else
    ExtTy := 'i8';
  EmitOp_VarLoad(L);
  EmitOp_VarLoad(R);
  EmitIns_IntExt(L, ExtTy, False);
  EmitIns_IntExt(R, ExtTy, False);
  Result.Name := TempVar;
  Result.TyStr := 'i1';
  Result.States := [];
  WriteCode('%s = %s %s %s, %s', [Result.Name, CharOpMaps[E.OpCode], ExtTy, L.Name, R.Name]);
end;

procedure TCodeGen.EmitOp_Currency(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  LT, RT: TType;
  Op, Va: string;
  NeedAdjust: boolean;

  procedure MulBy10k(var R: TVarInfo);
  var
    Va: string;
  begin
    Va := TempVar;
    WriteCode('%s = fmul %s %s, 10000.0', [Va, 'double', R.Name]);
    R.Name := Va;
  end;

  procedure DivBy10k(var R: TVarInfo);
  var
    Va: string;
  begin
    Va := TempVar;
    WriteCode('%s = fdiv %s %s, 10000.0', [Va, 'double', R.Name]);
    R.Name := Va;
  end;

  procedure ToDouble(T: TType; var R: TVarInfo; MulOrDiv: boolean);
  begin
    case T.TypeCode of
      typInt: EmitIns_Int2Flt(R, 'double', T.IsSigned);
      typNumeric: case TNumericType(T).Kind of
          numComp: EmitIns_Int2Flt(R, 'double', T.IsSigned);
          numCurrency: EmitIns_Int2Flt(R, 'double', True);
          else
            EmitIns_FltExt(R, 'double');
        end;
    end;
    if not MulOrDiv and (not T.IsCurrency) then
      MulBy10k(R);
  end;

begin
  L.States := [];
  R.States := [];
  EmitOp(TBinaryOp(E).Left, L);
  EmitOp(TBinaryOp(E).Right, R);
  EmitOp_VarLoad(L);
  EmitOp_VarLoad(R);
  if vasCurrConst in L.States then
    LT := FContext.FCurrencyType
  else
    LT := TBinaryOp(E).Left.Typ;
  if vasCurrConst in R.States then
    RT := FContext.FCurrencyType
  else
    RT := TBinaryOp(E).Right.Typ;
  ToDouble(LT, L, E.OpCode in [opcMUL, opcFDIV]);
  ToDouble(RT, R, E.OpCode in [opcMUL, opcFDIV]);
  NeedAdjust := (LT.IsCurrency) and (RT.IsCurrency) and (E.OpCode in [opcMUL, opcFDIV]);
  case E.OpCode of
    opcADD: Op := 'fadd';
    opcSUB: Op := 'fsub';
    opcMUL: Op := 'fmul';
    opcFDIV: Op := 'fdiv';
    opcNE: Op := 'fcmp une';
    opcEQ: Op := 'fcmp ueq';
    opcLT: Op := 'fcmp ult';
    opcLE: Op := 'fcmp ule';
    opcGT: Op := 'fcmp ugt';
    opcGE: Op := 'fcmp uge';
    else
      Assert(False, 'EmitOp_Currency');
  end;
  if E.OpCode in [opcNE..opcGE] then
  begin
    Result.Name := TempVar;
    Result.TyStr := 'i1';
    Result.States := [];
    WriteCode('%s = %s %s %s, %s', [Result.Name, Op, 'double', L.Name, R.Name]);
  end
  else
  begin
    va := TempVar;
    WriteCode('%s = %s %s %s, %s', [Va, Op, 'double', L.Name, R.Name]);
    Result.Name := Va;
    Result.TyStr := 'double';
    if NeedAdjust then
      DivBy10K(Result);
    Result.Name := TempVar;
    Result.TyStr := 'i64';
    Result.States := [];
    EmitCallSys(srRound, ['double'], [Result.Name], Va);
  end;
end;

procedure TCodeGen.EmitOp_Float(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  LT, RT: TType;
  Op: string;
begin
  L.States := [];
  R.States := [];
  EmitOp(TBinaryOp(E).Left, L);
  EmitOp(TBinaryOp(E).Right, R);
  LT := TBinaryOp(E).Left.Typ;
  RT := TBinaryOp(E).Right.Typ;
  EmitOp_VarLoad(L);
  EmitOp_VarLoad(R);
  if LT.IsInteger or LT.IsComp then
    EmitIns_Int2Flt(L, 'double', LT.IsSigned);
  if RT.IsInteger or RT.IsComp then
    EmitIns_Int2Flt(R, 'double', RT.IsSigned);
  case E.OpCode of
    opcADD: Op := 'fadd';
    opcSUB: Op := 'fsub';
    opcMUL: Op := 'fmul';
    opcFDIV: Op := 'fdiv';
    opcNE: Op := 'fcmp une';
    opcEQ: Op := 'fcmp ueq';
    opcLT: Op := 'fcmp ult';
    opcLE: Op := 'fcmp ule';
    opcGT: Op := 'fcmp ugt';
    opcGE: Op := 'fcmp uge';
    else
      Assert(False, 'EmitOp_Float');
  end;
  Result.Name := TempVar;
  if (LT.IsSingle) and (RT.IsSingle) then
    Result.TyStr := 'float'
  else
    Result.TyStr := 'double';
  Result.States := [];
  WriteCode('%s = %s %s %s, %s', [Result.Name, Op, Result.TyStr, L.Name, R.Name]);
end;

procedure TCodeGen.EmitOp_Index(E: TBinaryOp; var Result: TVarInfo);
var
  L: TVarInfo;
  I: integer;
  LowRange: int64;
  Items: array of TVarInfo;
  Va: string;
  T: TType;

  function GetLowRange(T: TType): int64;
  begin
    case T.TypeCode of
      typArray: Result := TArrayType(T).Range.RangeBegin;
      typString: if TStringType(T).Kind in [strAShort, strWShort] then
          Result := 0
        else
          Result := 1;
      else
        Result := 0;
    end;
  end;

begin
  SetLength(Items, TListOp(E.Right).Count);
  for I := 0
    to Length(Items) - 1 do
  begin
    EmitOp(TListOp(E.Right).Items[I], Items[I]);
    EmitOp_VarLoad(Items[I]);
    EmitIns_IntExt(Items[I], NativeIntStr, True);
  end;
  L.States := [];
  EmitOp(E.Left, L);
  EnsurePtr(L.TyStr, 'EmitOp_Index, left node must be ptr');
  T := E.Left.Typ;
  for I := 0 to High(Items) do
  begin
    if (T.TypeCode <> typArray) and not T.IsShortString then
      EmitOp_VarLoad(L);
    LowRange := GetLowRange(T);
    if LowRange <> 0 then
    begin
      Va := TempVar;
      WriteCode('%s = sub %s %s, %s', [Va, NativeIntStr, Items[I].Name, IntToStr(LowRange)]);
      Items[I].Name := Va;
    end;
    Va := TempVar;
    if (T.TypeCode = typArray) or T.IsShortString then
      WriteCode('%s = getelementptr %s, %s %s, %%SizeInt 0, %%SizeInt %s',
        [Va, L.TyStr.Replace('*', '') + StringOfChar('*', L.TyStr.CountChar('*') - 1), L.TyStr, L.Name, Items[I].Name])
    else
      WriteCode('%s = getelementptr %s, %s %s, %%SizeInt %s', [Va, L.TyStr.Replace('*', '') +
        StringOfChar('*', L.TyStr.CountChar('*') - 1), L.TyStr, L.Name, Items[I].Name]);
    case T.TypeCode of
      typArray: T := TArrayType(T).ElementType;
      typDynamicArray: T := TDynamicArrayType(T).ElementType;
      typString: case
          TStringType(T).Kind of
          strAnsi, strAShort: T := FContext.FAnsiCharType;
          else
            T := FContext.FWideCharType;
        end;
      typPAnsiChar: T := FContext.FAnsiCharType;
      typPWideChar: T := FContext.FWideCharType;
      typPointer:
      begin
        Assert(not TPointerType(T).IsUntype, 'EmitOp_Index, void ptr');
        T := TPointerType(T).RefType;
      end;
      else
        Assert(False, 'EmitOp_Index, operand can not be index');
    end;
    L.Name := Va;
    L.TyStr := TypeStr(T) + '*';
    L.States := [vasAddrOfVar];
  end;
  Result.Name := L.Name;
  Result.TyStr := L.TyStr;
  Result.States := L.States;
end;

procedure TCodeGen.EmitOp_Inst(E: TUnaryOp; var Result: TVarInfo);
begin
  EmitOp(E.Operand, Result);
  if vasAddrOfVar in Result.States then
  begin
    EmitOp_VarLoad(Result);
    Include(Result.States, vasAddrOfVar);
  end
  else
  begin
    EnsurePtr(Result.TyStr, 'EmitOp_Inst: %d, %d', [E.Coord.Row, E.Coord.Col]);
    Include(Result.States, vasAddrOfVar);
  end;
end;

procedure TCodeGen.EmitOp_Int(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  LT, RT: TType;
  ExtTy, Op: string;
  diffSign, resultSign: boolean;

  function ICmpOp(op: TOpCode; sign: boolean): string;
  begin
    case op
      of
      opcNE: Result := 'icmp ne';
      opcEQ: Result := 'icmp eq';
      opcLT: if sign then
          Result := 'icmp slt'
        else
          Result := 'icmp ult';
      opcLE: if sign then
          Result := 'icmp sle'
        else
          Result := 'icmp ule';
      opcGT: if sign then
          Result := 'icmp sgt'
        else
          Result := 'icmp ugt';
      opcGE: if sign then
          Result := 'icmp sge'
        else
          Result := 'icmp uge';
      else
        Assert(False, 'ICmpOp');
    end;
  end;

begin
  L.States := [];
  R.States := [];
  EmitOp(TBinaryOp(E).Left, L);
  EmitOp(TBinaryOp(E).Right, R);
  LT := TBinaryOp(E).Left.Typ;
  RT := TBinaryOp(E).Right.Typ;
  diffSign := LT.IsSigned <> RT.IsSigned;
  resultSign := LT.IsSigned or RT.IsSigned;
  case E.OpCode of
    opcSHR: ExtTy := TypeStr(LT);
    opcAND, opcOR, opcXOR, opcSHL: ExtTy := TypeStr(E.Typ);
    else
      if diffSign and not (E.OpCode in [opcNE..opcGE]) then
      begin
        ExtTy := TypeStr(E.Typ);
      end
      else
        ExtTy := 'i32';
  end;
  EmitOp_VarLoad(L);
  EmitOp_VarLoad(R);
  EmitIns_IntExt(L, ExtTy, LT.IsSigned, Format('%d,%d', [E.Coord.Row, E.Coord.Col]));
  if E.OpCode = opcSHR then
  begin
    if (RT.Size > LT.Size) then
      EmitIns_IntTrunc(R, ExtTy)
    else
      EmitIns_IntExt(R, ExtTy, RT.IsSigned);
  end
  else
    EmitIns_IntExt(R, ExtTy, RT.IsSigned);
  case E.OpCode of
    opcADD: Op := 'add';
    opcSUB: Op := 'sub';
    opcMUL: Op := 'mul';
    opcIDIV: Op := 'div';
    opcMOD: if resultSign then
        Op := 'srem'
      else
        Op := 'urem';
    opcAND: Op := 'and';
    opcOR: Op := 'or';
    opcXOR: Op := 'xor';
    opcSHL: Op := 'shl';
    opcSHR: Op := 'lshr';
    opcNE
    ..opcGE: Op := ICmpOp(E.OpCode, resultSign);
    else
      Assert(False, 'EmitOp_Int, invalid op');
  end;
  if (cdOverflowChecks in E.Switches) and (E.OpCode in [opcADD, opcSUB, opcMUL]) then
  begin
    Result.Name := TempVar;
    EmitOp_IntOvf(L, R, Result, E.OpCode, ltI32, LT.IsSigned or RT.IsSigned);
  end
  else if E.OpCode in [opcNE..opcGE] then
  begin
    Result.Name := TempVar;
    Result.TyStr := 'i1';
    Result.States := [];
    WriteCode('%s = %s %s %s, %s', [Result.Name, Op, ExtTy, L.Name, R.Name]);
  end
  else
  begin
    Result.Name := TempVar;
    Result.TyStr := ExtTy;
    Result.States := [];
    WriteCode('%s = %s %s %s, %s', [Result.Name, Op, Result.TyStr, L.Name, R.Name]);
  end;
end;

procedure TCodeGen.EmitOp_Int64(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  LT, RT: TType;
  Signed: boolean;

  function CmpCond(op: TOpCode; sign: boolean): string;
  begin
    case op of
      opcNE: Result := 'ne';
      opcEQ: Result := 'eq';
      opcLT: if sign then
          Result := 'slt'
        else
          Result := 'ult';
      opcLE: if sign then
          Result := 'sle'
        else
          Result := 'ule';
      opcGT: if sign then
          Result := 'sgt'
        else
          Result := 'ugt';
      opcGE: if sign then
          Result := 'sge'
        else
          Result := 'uge';
      else
        Assert(False, 'CmpCond');
    end;
  end;

  procedure Rel_BigInt;
  var
    pL, pR: ^TVarInfo;
    Op: TOpCode;
    cOp, s1, s2: string;
  begin
    if LT.IsSigned then
    begin
      pL := @L;
      pR := @R;
      Op := E.OpCode;
    end
    else
    begin
      pL := @R;
      pR := @L;
      case E.OpCode of
        opcLT: Op := opcGT;
        opcLE: Op := opcGE;
        opcGT: Op := opcLT;
        opcGE: Op := opcLE;
        else
          Op := E.OpCode;
      end;
    end;
    if Op in [opcGT, opcGE, opcEQ] then
      cOp := 'and'
    else
      cOp := 'or';
    s1 := TempVar;
    s2 := TempVar;
    if Op = opcNE then
      WriteCode('%s = icmp slt i64 %s, 0', [s1, pL^.Name])
    else if Op = opcEQ then
      WriteCode('%s = icmp sge i64 %s, 0', [s1, pL^.Name])
    else
      WriteCode('%s = icmp %s i64 %s, 0', [s1, CmpCond(Op, True), pL^.Name]);
    WriteCode('%s = icmp %s i64 %s, %s', [s2, CmpCond(Op, False), pL^.Name, pR^.Name]);
    Result.Name := TempVar;
    WriteCode('%s = %s i1 %s, %s', [Result.Name, cOp, s1, s2]);
  end;

begin
  EmitOp(TBinaryOp(E).Left, L);
  EmitOp(TBinaryOp(E).Right, R);
  LT := TBinaryOp(E).Left.Typ;
  RT := TBinaryOp(E).Right.Typ;
  Signed := LT.IsSigned or RT.IsSigned;
  EmitOp_VarLoad(L);
  EmitOp_VarLoad(R);
  EmitIns_IntExt(L, 'i64', LT.IsSigned);
  EmitIns_IntExt(R, 'i64', RT.IsSigned);
  Result.Name := TempVar;
  if E.OpCode in [opcNE..opcGE] then
    Result.TyStr := 'i1'
  else
    Result.TyStr := 'i64';
  Result.States := [];
  case E.OpCode
    of
    opcADD..opcMUL, opcAND, opcSHL, opcSHR: if (cdOverflowChecks in E.Switches) and
        (E.OpCode in [opcADD, opcSUB, opcMUL]) then
      begin
        EmitOp_IntOvf(L, R, Result, E.OpCode, ltI64, Signed);
      end
      else
      begin
        WriteCode('%s = %s i64 %s, %s', [Result.Name, ArithOpMaps[E.OpCode], L.Name, R.Name]);
      end;
    opcIDIV: EmitCallSys(srInt64Div, ['i64', 'i64'], [L.Name, R.Name], Result.Name);
    opcMOD: EmitCallSys(srInt64Mod, ['i64', 'i64'], [L.Name, R.Name], Result.Name);
    opcNE..opcGE: if LT.IsSigned = RT.IsSigned then
      begin
        WriteCode('%s = icmp %s i64 %s, %s', [Result.Name, CmpCond(E.OpCode, LT.IsSigned), L.Name, R.Name]);
      end
      else
      begin
        Rel_BigInt;
      end;
    else
      Assert(False, 'EmitOp_Int64');
  end;
end;

procedure TCodeGen.EmitOp_IntOvf(var L, R, Result: TVarInfo; Op: TAddSubMulOp; Ty: TLLVMIntType; IsSign: boolean);
const
  OpStr: array[opcADD..opcMUL, boolean] of string = (('uadd', 'sadd'), ('usub', 'ssub'), ('', ''), ('', ''), ('umul', 'smul'));
  llvm_instr: array[TLLVMIntType] of TLLVMIntrinsic = (llvm_ovfi8, llvm_ovfi16, llvm_ovfi32, llvm_ovfi64);
var
  TyStr, S, Lb1, Lb2: string;
begin
  Assert(Ty <= ltI64);
  Assert(Ty >= ltI8);
  Include(FIntrinsics, llvm_instr[Ty]);
  if Result.Name = '' then
    Result.Name := TempVar;
  TyStr := llvmTypeNames[Ty];
  WriteCode('%s = call {%s, i1} @llvm.%s.with.overflow.%s(%s %s, %s %s)',
    [Result.Name, TyStr, OpStr[Op, IsSign], TyStr, TyStr, L.Name, TyStr, R.Name]);
  S := TempVar;
  Lb1 := LabelStr;
  Lb2 := LabelStr;
  WriteCode('%s = extractvalue {%s, i1} %s, 1', [S, TyStr, Result.Name]);
  WriteCode('br i1 %s, label %%%s, label %%%s', [S, Lb1, Lb2]);
  WriteLabel(Lb1);
  EmitCallSys(srIntOverflow, [], []);
  WriteCode('unreachable');
  WriteLabel(Lb2);
  S := TempVar;
  WriteCode('%s = extractvalue {%s, i1} %s, 0', [S, TyStr, Result.Name]);
  Result.Name := S;
  Result.TyStr := TyStr;
  Result.States := [];
end;

procedure TCodeGen.EmitOp_Load(E: TSymbolOp; var Result: TVarInfo);
begin
  EmitOp_LoadRef(E.Reference, Result);
end;

procedure TCodeGen.EmitOp_LoadConst(E: TConstOp; var Result: TVarInfo);
begin
  EmitOp_LoadConstValue(E.Value, E.Typ, Result);
end;

procedure TCodeGen.EmitOp_LoadConstValue(const Value: TValueRec; T: TType; var Result: TVarInfo);
begin
  Result.States := [];
  case Value.VT of
    vtInt:
    begin
      Result.Name := IntToStr(Value.VInt);
      Result.TyStr := TypeStr(T);
    end;
    vtInt64:
    begin
      Result.Name := IntToStr(Value.VInt64);
      Result.TyStr := TypeStr(T);
    end;
    vtReal:
    begin
      Result.Name := FloatToStr(Value.VReal);
      Result.TyStr := 'double';
    end;
    vtBool:
    begin
      Result.Name := IntBoolStr[Value.VBool <> 0];
      Result.TyStr := 'i8';
    end;
    vtCurr:
    begin
      Result.Name := IntToStr(Value.VInt64);
      Result.TyStr := 'i64';
      Result.States := [vasCurrConst];
    end;
    vtAChr:
    begin
      Result.Name := IntToStr(Ord(Value.VAChr));
      Result.TyStr := 'i8';
    end;
    vtWChr:
    begin
      Result.Name := IntToStr(word(Value.VWChr));
      Result.TyStr := 'i16';
    end;
    vtStr: if Value.VStr = nil then
      begin
        Result.Name := 'null';
        Result.TyStr := 'i8*';
      end
      else
        Assert(False, 'EmitOp_LoadConstValue');
    vtWStr: if Value.VStr = nil then
      begin
        Result.Name := 'null';
        Result.TyStr := 'i16*';
      end
      else
        Assert(False, 'EmitOp_LoadConstValue');
    vtPtr: if Value.VPtr = nil then
      begin
        Result.Name := 'null';
        Result.TyStr := 'i8*';
      end
      else
      begin
        Result.Name := Format('inttoptr %SizeInt 0x%p to i8*', [Value.VPtr]);
        Result.TyStr := 'i8*';
      end;
    else
      Assert(False, 'EmitOp_LoadConstValue');
  end;
end;

procedure TCodeGen.EmitOp_LoadObj(E: TBaseOp; var Ret: TVarInfo);
begin
end;

procedure TCodeGen.EmitOp_LoadRef(Ref: TSymbol; var Result: TVarInfo);

  procedure LoadOutterArg;
  var
    Va: string;
    parentCntx: TEmitFuncContext;
  begin
    Assert(FCurCntx.Func.Level > TFuncParam(Ref).Level, 'EmitOp_LoadRef, load arg');
    parentCntx := TEmitFuncContext(FCntxList[TFuncParam(Ref).Level]);
    Va := TempVar;
    WriteCode('%s = getelementptr %s, %s* %%.fp%d, %%SizeInt 0, %%SizeInt %d', [Va, parentCntx.FrameTyStr,
      TFuncParam(Ref).Level, TFuncParam(Ref).Index]);
    if asByRef in TFuncParam(Ref).States then
    begin
      Result.Name := TempVar;
      Result.States := [vasAddrOfVar];
      Result.TyStr := TypeStr(TFuncParam(Ref).ParamType) + '*';
      WriteCode('%s = load %s, %s %s', [Result.Name, Result.TyStr.Replace('*', '') +
        StringOfChar('*', Result.TyStr.CountChar('*') - 1), Result.TyStr, Va]);
    end
    else
    begin
      Result.Name := Va;
      Result.States := [vasAddrOfVar];
      Result.TyStr := TypeStr(TFuncParam(Ref).ParamType) + '*';
    end;
  end;

  procedure LoadOutterVar;
  var
    parentCntx: TEmitFuncContext;
  begin
    Assert(FCurCntx.Func.Level > TFuncParam(Ref).Level, 'EmitOp_LoadRef, load var');
    parentCntx := TEmitFuncContext(FCntxList[TFuncParam(Ref).Level]);
    Result.Name := TempVar;
    Result.States := [vasAddrOfVar];
    Result.TyStr := TypeStr(TVariable(Ref).VarType) + '*';
    WriteCode('%s = getelementptr %s, %s* %%.fp%d, %%SizeInt 0, %%SizeInt %d',
      [Result.Name, parentCntx.FrameTyStr, TVariable(Ref).Level, TVariable(Ref).Index]);
  end;

  procedure LoadClassVmt(T: TClassType);
  var
    QualID: string;
  begin
    QualID := MangledName(T);
    Result.Name := Format('bitcast(i8** getelementptr(%%%s.$vmt.t, %%%s.$vmt.t* @%s.$vmt, %%SizeInt 0, %%SizeInt %d) to i8*)',
      [QualID, QualID, QualID, ast.ROOT_VMT_ENTRY_COUNT]);
    Result.TyStr := 'i8*';
    Result.States := [];
    AddExternalSymbol(T);
  end;

var
  T: TType;
begin
  case Ref.NodeKind of
    nkFuncParam: if TFuncParam(Ref).Level <> FCurCntx.Func.Level then
      begin
        LoadOutterArg;
      end
      else
      begin
        Result.Name := Format('%%%s.addr', [Ref.Name]);
        Result.States := [vasAddrOfVar];
        Result.TyStr := TypeStr(TFuncParam(Ref).ParamType) + '*';
      end;
    nkVariable: if TVariable(Ref).Level <> FCurCntx.Func.Level then
      begin
        LoadOutterVar;
      end
      else if vaSelf in TVariable(Ref).VarAttr then
      begin
        Result.Name := '%Self';
        Result.TyStr := 'i8*';
        Result.States := [];
      end
      else if (vsResultAddr in TVariable(Ref).States) then
      begin
        Result.Name := '%Result.addr';
        Result.TyStr := TypeStr(TVariable(Ref).VarType) + '*';
        Result.States := [vasAddrOfVar];
      end
      else
      if vaLocal in TVariable(Ref).VarAttr then
      begin
        Result.Name := '%' + Ref.Name + '.addr';
        Result.TyStr := TypeStr(TVariable(Ref).VarType) + '*';
        Result.States := [vasAddrOfVar];
      end
      else
      begin
        Result.Name := '@' + MangledName(Ref);
        Result.TyStr := TypeStr(TVariable(Ref).VarType) + '*';
        Result.States := [vasAddrOfVar];
        AddExternalSymbol(Ref);
      end;
    nkField: Assert(False, 'Internal Error 11102018');
    nkConstant:
    begin
      T := TConstant(Ref).ConstType;
      if T.IsInteger then
      begin
        Result.Name := ValToStr(TConstant(Ref).Value);
        Result.TyStr := TypeStr(T);
      end
      else if T.IsBoolean then
      begin
        Result.Name := BoolStr[ValToBool(TConstant(Ref).Value)];
        Result.TyStr := 'i1';
      end
      else if T.IsReal then
      begin
        Result.Name := ValToStr(TConstant(Ref).Value);
        Result.TyStr := TypeStr(T);
      end
      else if T.TypeCode in [typString, typPAnsiChar, typPWideChar] then
      begin
        Result.Name := MangledName(Ref);
        case T.TypeCode of
          typPAnsiChar, typPWideChar: Result.Name :=
              Format('getelementptr(%%%s.ty, %%%s.ty* @%0:s, %%SizeInt 0, %%SizeInt 0)', [Result.Name, Result.Name]);
          typString: case TStringType(T).Kind of
              strAnsi, strUnicode: Result.Name :=
                  Format('getelementptr(%%%s.ty, %%%s.ty* @%0:s, %%SizeInt 0, %%SizeInt 2, %%SizeInt 0)', [Result.Name, Result.Name]);
              strWide: Result.Name := Format('getelementptr(%%%s.ty, %%%s.ty* @%0:s, %%SizeInt 0, %%SizeInt 1, %%SizeInt 0)',
                  [Result.Name, Result.Name]);
              strAShort, strWShort:
              begin
                Result.Name := Format('getelementptr(%%%s.ty, %%%s.ty* @%0:s, %%SizeInt 0)', [Result.Name, Result.Name]);
                Result.TyStr := TypeStr(T) + '*';
              end;
            end;
        end;
        if Result.TyStr = '' then
          Result.TyStr := TypeStr(T);
      end
      else
        Assert(False);
    end;
    nkType: case TType(Ref).TypeCode of
        typClass: LoadClassVmt(TClassType(Ref));
        typClassRef: LoadClassVmt(TClassRefType(Ref).RefType);
        else
          Assert(False, 'EmitOp_LoadRef, nkType');
      end;
    nkEnumElement:
    begin
      case TEnumValue(Ref).EnumType.Size of
        1: Result.TyStr := 'i8';
        2: Result.TyStr := 'i16';
        else
          Result.TyStr := 'i32';
      end;
      Result.Name := IntToStr(TEnumValue(Ref).Value);
      Result.
        States := [];
    end
    else
      Assert(False, 'EmitOp_LoadRef');
  end;
end;

procedure TCodeGen.EmitOp_LoadSelf(var Result: TVarInfo);
begin
  Result.Name := '%Self';
  Result.TyStr := 'i8*';
  Result.States := [];
end;

procedure TCodeGen.EmitOp_Member(E: TBinaryOp; var Result: TVarInfo);
var
  LV: TVarInfo;
  Sym: TSymbol;
  Va: string;
  isRef: boolean;
begin
  LV.States := [];
  EmitOp(E.Left, LV);
  Sym := TSymbolOp(E.Right).Reference;
  case Sym.NodeKind of
    nkField:
    begin
      assert(Sym.Parent.NodeKind = nkType, 'EmitOp_Member');
      isRef := not (TType(Sym.Parent).TypeCode in [typObject, typRecord]);
      if isRef then
        EmitOp_VarLoad(LV);
      Va := TempVar;
      Result.Name := TempVar;
      Result.TyStr := TypeStr(E.Typ) + '*';
      Result.States := [vasAddrOfVar];
      Result.Align := IntToStr(TField(Sym).AlignOfParent);
      if isRef then
        WriteCode('%s = getelementptr %s, %s %s, %%SizeInt %d', [Va, LV.TyStr.Replace('*', '') +
          StringOfChar('*', LV.TyStr.CountChar('*') - 1), LV.TyStr, LV.Name, TField(Sym).Offset])
      else
        WriteCode('%s = getelementptr %s, %s %s, %%SizeInt 0, %%SizeInt %d',
          [Va, LV.TyStr.Replace('*', '') + StringOfChar('*', LV.TyStr.CountChar('*') - 1),
          LV.TyStr, LV.Name, TField(Sym).Offset]);
      WriteCode('%s = bitcast i8* %s to %s', [Result.Name, Va, Result.TyStr]);
    end;
    else
      Assert(False, 'EmitOp_Member: Expect field');
  end;
end;

procedure TCodeGen.EmitOp_Neg(E: TUnaryOp; var Result: TVarInfo);
var
  V: TVarInfo;

  procedure IntNeg;
  begin
    Result.TyStr := TypeStr(E.Operand.Typ);
    Result.States := [];
    WriteCode('%s = sub %s 0, %s', [Result.Name, Result.TyStr, V.Name]);
  end;

begin
  V.States := [];
  EmitOp(E.Operand, V);
  EmitOp_VarLoad(V);
  Result.Name := TempVar;
  case E.Typ.TypeCode of
    typInt: IntNeg;
    typNumeric: if TNumericType(E.Typ).Kind in [numComp, numCurrency] then
        IntNeg
      else
      begin
        Result.TyStr := TypeStr(E.Operand.Typ);
        Result.States := [];
        WriteCode('%s = fsub %s 0.0, %s', [Result.Name, Result.TyStr, V.Name]);
      end;
    else
      Assert(False, 'EmitOp_Neg');
  end;
end;

procedure TCodeGen.EmitOp_Not(E: TUnaryOp; var Result: TVarInfo);
var
  V: TVarInfo;
  Va: string;
const
  TrueValues: array[boolean] of string = ('-1', '1');
begin
  V.States := [];
  EmitOp(E.Operand, V);
  EmitOp_VarLoad(v);
  case E.Typ.TypeCode of
    typInt:
    begin
      Result.Name := TempVar;
      Result.States := [];
      Result.TyStr := TypeStr(E.Operand.Typ);
      WriteCode('%s = xor %s %s, -1', [Result.Name, Result.TyStr, V.Name]);
    end;
    typBool:
    begin
      Va := TempVar;
      WriteCode('; not op');
      WriteCode('%s = icmp ne %s %s, 0', [Va, V.TyStr, V.Name]);
      Result.Name := TempVar;
      Result.States := [];
      Result.TyStr := TypeStr(E.Operand.Typ);
      WriteCode('%s = select i1 %s, %s 0, %s %s', [Result.Name, Va, Result.TyStr, Result.TyStr,
        TrueValues[E.Operand.Typ.IsStdBool]]);
    end;
    else
      Assert(False, 'EmitOp_Not');
  end;
end;

procedure TCodeGen.EmitOp_ProcAddr(E: TUnaryOp; var ResultVar: TVarInfo);
var
  Sym: TSymbol;
  IsMeth: boolean;
  Va1, Va2, FunName, SelfPtr: string;
  Fun: TFunctionDecl;
  FunT: TProceduralType;
  Left: TBaseOp;
  ParentT: TType;
  LV: TVarInfo;
  IsCallBase, IsVirtual, IsTypePrefix{, IsClassRefPrefix}: Boolean;
begin
  Sym := E.Operand.GetReference;
  Assert(Sym.NodeKind in [nkMethod, nkFunc, nkExternalFunc]);
  Fun := TFunctionDecl(Sym);
  FunT := Fun.ProceduralType;
  IsMeth := FunT.IsMethodPointer;
  Left := e.Operand;
  if (Fun.NodeKind = nkExternalFunc) and (TExternalFunction(Fun).RoutineName <> '') then
    FunName := '@' + TExternalFunction(Fun).RoutineName
  else
    FunName := '@' + MangledName(Fun);
  if IsMeth then
  begin
    IsCallBase := False;
    IsVirtual := fmVirtual in Fun.Modifiers;
    IsTypePrefix :=
      (Left.OpCode = opcMember) and (TBinaryOp(Left).Left.IsTypeSymbol);
    //IsClassRefPrefix := (Left.OpCode = opcMember) and (TBinaryOp(Left).Left.Typ.TypeCode = typClassRef);
    Assert(Fun.Parent.NodeKind = nkType, 'Method parent err');
    ParentT := TType(Fun.Parent);
    if Left.OpCode = opcSYMBOL then
    begin
      LV.Name := '%Self';
      LV.TyStr := 'i8*';
      LV.States := [];
    end
    else if Left.OpCode = opcMEMBER then
    begin
      EmitOp(TBinaryOp(Left).Left, LV);
      if ParentT.TypeCode in [typInterface, typClass] then
        EmitOp_VarLoad(LV);
      EnsurePtr(LV.TyStr, 'Instance of method is not ptr');
    end
    else
      Assert(False, 'EnitOp_ProcAddr, invalid left node');
    if (ParentT.TypeCode = typClass) and (saClass in Fun.Attr) and not IsTypePrefix and not FTopCntx.IsClassFunc then
    begin
      if LV.TyStr <> 'i8**' then
      begin
        Va1 := TempVar;
        WriteCode('%s = bitcast %s %s to i8**', [Va1, LV.TyStr, LV.Name]);
      end
      else
        Va1 := LV.Name;
      Va2 := TempVar;
      WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
      LV.Name := Va2;
      LV.TyStr := 'i8*';
      LV.States := [];
    end;
    if (IsVirtual or (ParentT.TypeCode = typInterface)) and not IsCallBase and not IsTypePrefix then
    begin
      if not (saClass in Fun.Attr) then
      begin
        if LV.TyStr <> 'i8***' then
        begin
          Va1 := TempVar;
          WriteCode('%s = bitcast %s %s to i8***', [Va1, LV.TyStr, LV.Name]);
        end
        else
          Va1 := LV.Name;
        if parentT.TypeCode = typObject then
        begin
          Va2 := TempVar;
          WriteCode('%s = getelementptr i8**, i8*** %s, %%SizeInt %d',
            [Va2, Va1, TObjectType(parentT).VmtOffset div FModule.PointerSize]);
          Va1 := Va2;
        end;
        Va2 := TempVar;
        WriteCode('%s = load i8**, i8*** %s', [Va2, Va1]);
      end
      else
      begin
        Va2 := TempVar;
        WriteCode('%s = bitcast %s %s to i8**', [Va2, LV.TyStr, LV.Name]);
      end;
      Va1 := TempVar;
      WriteCode('%s = getelementptr i8*, i8** %s, %%SizeInt %d', [Va1, Va2, TMethod(Fun).VTIndex]);
      Va2 := TempVar;
      WriteCode('%s = load i8*, i8** %s', [Va2, Va1]);
      FunName := Va2;
    end;
    if LV.TyStr <> 'i8*' then
    begin
      Va1 := TempVar;
      WriteCode('%s = bitcast %s %s to i8*', [Va1, LV.TyStr, LV.Name]);
      SelfPtr := Va1;
    end
    else
      SelfPtr := LV.Name;
    Va1 := TempVar;
    WriteCode('%s = bitcast %s %s to i8*', [Va1, ProcTypeStr(FunT), FunName]);
    FunName := Va1;
    Va1 := TempVar;
    WriteCode('%s = insertvalue [2 x i8*] undef, i8* %s, 0', [Va1, FunName]);
    Va2 := TempVar;
    WriteCode('%s = insertvalue [2 x i8*] %s, i8* %s, 1', [Va2, Va1, SelfPtr]);
    VarInfoInit(ResultVar);
    ResultVar.Name := Va2;
    ResultVar.TyStr := '[2 x i8*]';
  end
  else
  begin
    Va1 := TempVar;
    WriteCode('%s = bitcast %s %s to i8*', [Va1, ProcTypeStr(FunT), FunName]);
    VarInfoInit(ResultVar);
    ResultVar.Name := Va1;
    ResultVar.TyStr := 'i8*';
  end;
end;

procedure TCodeGen.EmitOp_Ptr(E: TBaseOp; var Result: TVarInfo);
var
  L, R: TVarInfo;
  LT, RT: TType;
  Va, Va2: string;

  procedure PtrAdd(const LV, RV: TVarInfo);
  begin
    Result.Name := TempVar;
    WriteCode('%s = getelementptr %s, %s %s, %s %s', [Result.Name, LV.TyStr.Replace('*', '') +
      StringOfChar('*', LV.TyStr.CountChar('*') - 1), LV.TyStr, LV.Name, RV.TyStr, RV.Name]);
    Result.States := [];
    Result.TyStr := LV.TyStr;
  end;

  procedure VarLoadMethPtr(var V: TVarInfo);
  var
    va1, va2: string;
  begin
    va1 := TempVar;
    va2 := TempVar;
    WriteCode('%s = bitcast %s %s to i8**', [va1, V.TyStr, V.Name]);
    WriteCode('%s = load i8*, i8** %s', [va2, va1]);
    V.Name := va2;
    V.TyStr := 'i8*';
    V.States := [];
  end;

  function SizeOfRef(T: TType): integer;
  begin
    case T.TypeCode of
      typPointer: if TPointerType(T).RefType = nil then
          Result := 1
        else
          Result := TPointerType(T).RefType.Size;
      typPAnsiChar: Result := 1;
      typPWideChar: Result := 2;
      else
        Result := 1;
    end;
  end;

const
  PtrCompConds: array[opcNE..opcGE] of string = ('ne', 'eq', 'ult', 'ule', 'ugt', 'uge');
begin
  L.States := [];
  R.States := [];
  EmitOp(TBinaryOp(E).Left, L);
  EmitOp(TBinaryOp(E).Right, R);
  LT := TBinaryOp(E).Left.Typ;
  RT := TBinaryOp(E).Right.Typ;
  if LT.IsMethodPointer then
    VarLoadMethPtr(L)
  else
    Self.EmitOp_VarLoad(L);
  if RT.IsMethodPointer then
    VarLoadMethPtr(R)
  else
    Self.EmitOp_VarLoad(R);
  if E.OpCode = opcADD then
  begin
    if (LT.TypeCode = typInt) then
    begin
      Assert(RT.IsPointer, 'EmitOp_Ptr: expected rightop is ptr');
      PtrAdd(R, L);
    end
    else
    begin
      Assert(RT.TypeCode = typInt, 'EmitOp_Ptr: expected rightop is int');
      Assert(LT.IsPointer, 'EmitOp_Ptr: expected leftop is ptr');
      PtrAdd(L, R);
    end;
  end
  else
  if E.OpCode = opcSUB then
  begin
    if LT.IsPointer and (RT.TypeCode = typInt) then
    begin
      Va := TempVar;
      WriteCode('%s = sub %s 0, %s', [Va, R.TyStr, R.Name]);
      R.Name := Va;
      PtrAdd(L,
        R);
    end
    else
    begin
      Assert(LT.IsPointer and RT.IsPointer, 'EmitOp_Ptr: expected op is ptr');
      Self.EmitIns_Ptr2Int(L, TypeStr(FContext.FNativeIntType));
      Self.EmitIns_Ptr2Int(R, TypeStr(FContext.FNativeIntType));
      Va := TempVar;
      WriteCode('%s = sub %s %s, %s', [Va, L.TyStr, L.Name, R.Name]);
      if SizeOfRef(LT) > 1 then
      begin
        Va2 := TempVar;
        WriteCode('%s = sdiv %s %s, %d', [Va2, L.TyStr, Va, SizeOfRef(LT)]);
        Result.Name := Va2;
      end
      else
        Result.Name := Va;
      Result.TyStr := L.TyStr;
      Result.States := [];
    end;
  end
  else
  begin
    Assert(E.OpCode in [opcNE..opcGE], 'EmitOp_Ptr: expected op in [opcNE..opcGE]');
    Assert((LT.IsPointerBased or LT.IsProcedural) and (RT.IsPointerBased or RT.IsProcedural),
      'EmitOp_Ptr: expected op is ptr');
    Assert(E.Typ.TypeCode = typBool, 'EmitOp_Ptr: expected result is bool');
    if R.TyStr <> L.TyStr then
      EmitIns_Bitcast(R, L.TyStr);
    Result.Name := TempVar;
    WriteCode('%s = icmp %s %s %s, %s', [Result.Name, PtrCompConds[E.OpCode], L.TyStr, L.Name, R.Name]);
    Result.TyStr := 'i1';
    Result.States := [];
  end;
end;

procedure TCodeGen.EmitOp_VarLoad(const Src: TVarInfo; out Des: TVarInfo);
var
  Align: byte;
begin
  if vasAddrOfVar in Src.States then
  begin
    EnsurePtr(Src.TyStr, 'EmitOp_VarLoad, pointer expected');
    Des.Name := TempVar;
    Des.TyStr := Src.TyStr;
    Des.States := Src.States;
    Des.Align := Src.Align;
    Align := StrToIntDef(Des.Align, 0);
    if Align = 0 then
      WriteCode('%s = load %s, %s %s', [Des.Name, Src.TyStr.Replace('*', '') + StringOfChar(
        '*', Src.TyStr.CountChar('*') - 1), Src.TyStr, Src.Name])
    else
    begin
      Assert(Align in [1, 2, 4, 8, 16, 32, 64, 128]);
      WriteCode('%s = load %s, %s %s, align %d', [Des.Name, Src.TyStr.Replace('*', '') +
        StringOfChar('*', Src.TyStr.CountChar('*') - 1), Src.TyStr, Src.Name, Align]);
      //WriteCode('%s = load %s, %s %s', [Des.Name, Src.TyStr.Replace('*', '') +
        //StringOfChar('*', Src.TyStr.CountChar('*') - 1), Src.TyStr, Src.Name]);
    end;
    RemoveLastChar(Des.TyStr);
    Exclude(Des.States, vasAddrOfVar);
  end
  else
  begin
    VarInfoCopy(Src, des);
  end;
end;

procedure TCodeGen.EmitOp_VarLoad(var Result: TVarInfo);
var
  v: string;
begin
  if vasAddrOfVar in Result.States then
  begin
    EnsurePtr(Result.TyStr, 'EmitOp_VarLoad, pointer expected');
    v := TempVar;
    if Result.TyStr <> 'void (i8, i8*)**' then
      WriteCode('%s = load %s, %s %s', [v, Result.TyStr.Replace('*', '') + StringOfChar(
        '*', Result.TyStr.CountChar('*') - 1), Result.TyStr, Result.Name])
    else
      WriteCode('%s = load %s, %s %s', [v, 'void (i8, i8*)*', 'void (i8, i8*)**', Result.Name]);
    Result.Name := v;
    RemoveLastChar(Result.TyStr);
    Exclude(Result.States, vasAddrOfVar);
  end;
end;

procedure TCodeGen.EmitRangeCheck(var V: TVarInfo; RT, LT: TType);

  function GetRange(LT: TType; out LowVal, HighVal: int64): boolean;
  var
    RngTyp: TSubrangeType;
  begin
    Result := True;
    case LT.TypeCode of
      typSubrange:
      begin
        LowVal := TSubrangeType(LT).RangeBegin;
        HighVal := TSubrangeType(LT).RangeEnd;
      end;
      typEnum:
      begin
        LowVal := TEnumType(LT).SubrangeType.RangeBegin;
        HighVal := TEnumType(LT).SubrangeType.RangeEnd;
      end;
      else
        RngTyp := FContext.GetSubrangeType(LT);
        if RngTyp <> nil then
        begin
          LowVal := RngTyp.RangeBegin;
          HighVal := RngTyp.RangeEnd;
        end
        else
          Result := False;
    end;
  end;

var
  LowVal, HighVal: Int64;
  Va, Va2, OkLabel, FailLabel: string;
begin
  if not GetRange(LT, LowVal, HighVal) then
    Exit;
  FailLabel := LabelStr;
  OkLabel := LabelStr;
  if not (LT.TypeCode in [typSubrange, typBool]) and (LT.Size = RT.Size) then
  begin
    Va := TempVar;
    WriteCode('%s = icmp sgt i32 %%%s, -1', [Va, V.Name]);
    WriteCode('br i1 %s, label %%%s, label %%%s', [Va, OkLabel, FailLabel]);
  end
  else
  begin
    if LowVal <> 0 then
    begin
      Va := TempVar;
      WriteCode('%s = add %s %s, %s', [Va, V.TyStr, V.Name, IntToStr(0 - LowVal)]);
    end
    else
      Va := V.Name;
    Va2 := TempVar;
    WriteCode('%s = icmp ule %s %s, %s', [Va2, V.TyStr, Va, IntToStr(HighVal - LowVal)]);
    WriteCode('br i1 %s, label %%%s, label %%%s', [Va2, OkLabel, FailLabel]);
  end;
  WriteLabel(FailLabel);
  EmitCallSys(srOutOfRange, [], []);
  WriteCode('unreachable');
  WriteLabel(OkLabel);
end;

procedure TCodeGen.EmitRtti_Class(T: TClassType);
var
  QualID: string;
  I: integer;
begin
  QualID := MangledName(T);
  EmitStrA(True, QualID + '.$name', T.Name);
  WriteDecl('%%%s.$vmt.t = type [%d x i8*]', [QualID, T.VmtEntryCount + 11]);
  WriteDecl('@%s.$vmt = global %%%s.$vmt.t [', [QualID, QualID]);
  WriteDecl('  i8* bitcast(i8** getelementptr(%%%s.$vmt.t, %%%s.$vmt.t* @%s.$vmt, %%SizeInt 0, %%SizeInt 19) to i8*)',
    [QualID, QualID, QualID]);
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* null');
  WriteDecl('  ,i8* getelementptr({%%SizeInt, %%SizeInt, [%d x i8]}, {%%SizeInt, %%SizeInt, [%d x i8]}* @%s.$name, %%SizeInt 0, i32 2, %%SizeInt 0)', [Length(T.Name) + 1, Length(T.Name) + 1, QualID]);
  WriteDecl('  ,i8* inttoptr(%%SizeInt %d to i8*)', [T.ObjectSize]);
  if not Assigned(T.Base) then
    WriteDecl('  ,i8* null')
  else
    WriteDecl('  ,i8* bitcast(i8** getelementptr(%%%0:s.$vmt.t, %%%0:s.$vmt.t* @%0:s.$vmt, %%SizeInt 0, %%SizeInt 0) to i8*)',
      [MangledName(T.Base), MangledName(T.Base), MangledName(T.Base)]);
  WriteDecl(';--- vmt start');
  for I := 0 to T.VmtEntryCount - 1 do
  begin
    if Assigned(T.Vmt[I]) then
    begin
      WriteDecl('  ,i8* bitcast(%s @%s to i8*)', [ProcTypeStr(T.Vmt[I].ProceduralType), MangledName(T.Vmt[I])]);
      AddExternalSymbol(T.Vmt[I]);
    end
    else
      WriteDecl('  ,i8* null');
  end;
  WriteDecl(']');
end;

procedure TCodeGen.EmitRtti_Class_External(T: TClassType);
var
  QualID: string;
begin
  QualID := MangledName(T);
  WriteDecl('%%%s.$vmt.t = type [%d x i8*]', [QualID, T.VmtEntryCount + 11]);
  WriteDecl('@%s.$vmt = external global %%%s.$vmt.t', [QualID, QualID]);
end;

procedure TCodeGen.EmitRtti_Intf(T: TInterfaceType);
begin
end;

procedure TCodeGen.EmitRtti_Intf_External(T: TInterfaceType);
begin
end;

procedure TCodeGen.EmitRtti_Object(T: TObjectType);
begin
end;

procedure TCodeGen.EmitRtti_Object_External(T: TObjectType);
begin
end;

procedure TCodeGen.EmitRtti_Record(T: TRecordType);
begin
end;

procedure TCodeGen.EmitRtti_Record_External(T: TRecordType);
begin
end;

procedure TCodeGen.EmitStrA(pub: boolean; const Name, s: string; emitTy: boolean);
var
  size: integer;
  ty: string;
begin
  size := Length(s) + 1;
  if emitTy then
  begin
    WriteDecl('%%%s.ty = type {%%SizeInt, %%SizeInt, [%d x i8]}', [Name, size]);
    ty := '%' + Name + '.ty';
  end
  else
    ty := Format('{%%SizeInt, %%SizeInt, [%d x i8]}', [size]);
  WriteDecl(Format('@%s = %s unnamed_addr constant %s {%%SizeInt -1, %%SizeInt %d, [%d x i8] c"%s"}',
    [Name, Visibility[pub], ty, size - 1, size, EncodeAStr(s)]));
end;

procedure TCodeGen.EmitStrPa(pub: boolean; const Name, s: string; emitTy: boolean);
var
  chCount: integer;
  ty: string;
begin
  chCount := Length(s) + 1;
  if emitTy then
  begin
    WriteDecl(Format('%%%s.ty = type [%d x i8]', [Name, chCount]));
    ty := '%' + Name + '.ty';
  end
  else
    ty := Format('[%d x i8]', [chCount]);
  WriteDecl(Format('@%s = %s unnamed_addr constant %s c"%s"', [Name, Visibility[False], ty, EncodeAStr(s)]));
end;

procedure TCodeGen.EmitStrPw(pub: boolean; const Name: string; const s: WideString; emitTy: boolean);
var
  chCount: integer;
  ty: string;
begin
  chCount := Length(s) + 1;
  if emitTy then
  begin
    WriteDecl(Format('%%%s.ty = type [%d x i16]', [Name, chCount]));
    ty := '%' + Name + '.ty';
  end
  else
    ty := Format('[%d x i16]', [chCount]);
  WriteDecl(Format('@%s = %s unnamed_addr constant %s [%s]', [Name, Visibility[False], ty, EncodeWStr(s)]));
end;

procedure TCodeGen.EmitStrU(pub: boolean; const Name: string; const s: WideString; emitTy: boolean = False);
var
  ChCount, ByteCount: integer;
  ty: string;
begin
  ChCount := Length(s) + 1;
  ByteCount := ChCount * 2;
  if emitTy then
  begin
    WriteDecl('%%%s.ty = type {%%SizeInt, %%SizeInt, [%d x i16]}', [Name, chCount]);
    ty := '%' + Name + '.ty';
  end
  else
    ty := Format('{%%SizeInt, %%SizeInt, [%d x i16]}', [chCount]);
  WriteDecl(Format('@%s = %s unnamed_addr constant %s {%%SizeInt -1, %%SizeInt %d, [%d x i16] [%s]}',
    [Name, Visibility[pub], ty, ByteCount, ChCount, EncodeWStr(s)]));
end;

procedure TCodeGen.EmitStrW(pub: boolean; const Name: string; const s: WideString; emitTy: boolean);
var
  ChCount, ByteCount: integer;
  ty: string;
begin
  ChCount := Length(s) + 1;
  ByteCount := ChCount * 2;
  if emitTy then
  begin
    WriteDecl('%%%s.ty = type {%%SizeInt, [%d x i16]}', [Name, chCount]);
    ty :=
      '%' + Name + '.ty';
  end
  else
    ty := Format('{%%SizeInt, [%d x i16]}', [chCount]);
  WriteDecl(Format('@%s = %s unnamed_addr constant %s {%%SizeInt %d, [%d x i16] [%s]}',
    [Name, Visibility[pub], ty, ByteCount, ChCount, EncodeWStr(s)]));
end;

procedure TCodeGen.EmitSymbolDecl(Sym: TSymbol);
begin
  case Sym.NodeKind of
    nkType: EmitTypeDecl(TType(Sym));
    nkVariable: EmitGlobalVarDecl(TVariable(Sym));
    nkExternalFunc: EmitFunc(TFunctionDecl(Sym));
    nkFunc, nkMethod: Emit(TFunction(Sym));
  end;
end;

procedure TCodeGen.EmitSysTypeInfo;
type
  TTypeKind = (tkUnknown, tkInteger, tkChar, tkEnumeration, tkFloat, tkString, tkSet, tkClass,
    tkMethod, tkWChar, tkLString, tkWString, tkVariant, tkArray, tkRecord, tkInterface, tkInt64,
    tkDynArray, tkUnicodeString);
  TOrdType = (otSByte, otUByte, otSWord, otUWord, otSLong, otULong);
  TFloatType = (ftSingle, ftDouble, ftExtended, ftComp, ftCurr);

  procedure EmitIntTypeInfo(const Name: string; tk: TTypeKind; ot: TOrdType; MaxV, MinV: cardinal);
  var
    llvmtyp: string;
  begin
    llvmtyp := Format('<{i8, i8, [%d x i8], i8, i32, i32}>', [Length(Name)]);
    WriteDecl('@System.%s.$typeinfo.data = unnamed_addr constant %s <{' +
      'i8 %d, i8 %d, [%d x i8] c"%s", i8 %d, i32 %d, i32 %d}>', [Name, llvmtyp, Ord(tk),
      Length(Name), Length(Name), EncodeAStr(Name, False), Ord(ot), MinV, MaxV]);
    WriteDecl('@System.%s.$typeinfo = global i8* bitcast(%s* ' + '@System.%s.$typeinfo.data to i8*)',
      [Name, llvmtyp, Name]);
  end;

  procedure EmitInt64TypeInfo(const Name: string; tk: TTypeKind; ot: TOrdType; MaxV, MinV: int64);
  var
    llvmtyp: string;
  begin
    llvmtyp := Format('<{i8, i8, [%d x i8], i8, i64, i64}>', [Length(Name)]);
    WriteDecl('@System.%s.$typeinfo.data = unnamed_addr constant %s <{' +
      'i8 %d, i8 %d, [%d x i8] c"%s", i8 %d, i64 %d, i64 %d}>', [Name, llvmtyp, Ord(tk),
      Length(Name), Length(Name), EncodeAStr(Name, False), Ord(ot), MinV, MaxV]);
    WriteDecl('@System.%s.$typeinfo = global i8* bitcast(%s* ' + '@System.%s.$typeinfo.data to i8*)',
      [Name, llvmtyp, Name]);
  end;

  procedure EmitSimple(const Name: string; tk: TTypeKind);
  var
    llvmtyp: string;
  begin
    llvmtyp := Format('<{i8, i8, [%d x i8]}>', [Length(Name)]);
    WriteDecl('@System.%s.$typeinfo.data = unnamed_addr constant %s <{' + 'i8 %d, i8 %d, [%d x i8] c"%s"}>',
      [Name, llvmtyp, Ord(tk), Length(Name), Length(Name), EncodeAStr(Name, False)]);
    WriteDecl('@System.%s.$typeinfo = global i8* bitcast(%s* ' + '@System.%s.$typeinfo.data to i8*)',
      [Name, llvmtyp, Name]);
  end;

begin
  EmitIntTypeInfo('Shortint', tkInteger, otSByte, $80, $7f);
  EmitIntTypeInfo('Byte', tkInteger, otUByte, 0, 255);
  EmitIntTypeInfo('Smallint', tkInteger, otSWord, $8000, $7fff);
  EmitIntTypeInfo('Word', tkInteger, otUWord, 0, $ffff);
  EmitIntTypeInfo('Longint', tkInteger, otSLong, $80000000, $7fffffff);
  EmitIntTypeInfo('LongWord', tkInteger, otULong, 0, $ffffffff);
  EmitIntTypeInfo('Integer', tkInteger, otSLong, $80000000, $7fffffff);
  EmitIntTypeInfo('Cardinal', tkInteger, otULong, 0, $ffffffff);
  EmitInt64TypeInfo('Int64', tkInt64, otSLong, int64($8000000000000000), int64($7fffffffffffffff));
  EmitInt64TypeInfo('UInt64', tkInt64, otULong, 0, int64($ffffffffffffffff));
  if FContext.FStringType.Kind = strAnsi then
    EmitSimple('String', tkLString)
  else
    EmitSimple('String', tkUnicodeString);
  EmitSimple('AnsiString', tkLString);
  EmitSimple('WideString', tkWString);
  EmitSimple('UnicodeString', tkUnicodeString);
  EmitSimple('Variant', tkVariant);
  EmitSimple('OleVariant', tkVariant);
end;

procedure TCodeGen.EmitTypeDecl(T: TType);

  procedure EmitStructTypeDecl(T: TType);
  begin
    WriteDecl(Format('%%%s = type [%d x i8]', [MangledName(T), int64(T.Size)]));
  end;

  procedure EmitProcTypeDecl(T: TProceduralType);
  begin
    if T.IsMethodPointer then
      WriteDecl(Format('%%%s = type [2 x i8*]', [MangledName(T)]))
    else
      WriteDecl(ProcTypeStr(T, MangledName(T)));
  end;

  function ArrayTypeStr(T: TArrayType): string;
  var
    Size: int64;
  begin
    Size := T.Range.RangeEnd - T.Range.RangeBegin + 1;
    case T.ElementType.TypeCode of
      typArray: Result := Format('[%d x %s]', [Size, ArrayTypeStr(TArrayType(T.ElementType))]);
      else
        Result := Format('[%d x %s]', [Size, TypeStr(T.ElementType)]);
    end;
  end;

  procedure EmitArrayTypeDecl(T: TArrayType);
  var
    s: string;
  begin
    s := ArrayTypeStr(T);
    WriteDecl(Format('%%%s = type %s', [MangledName(T), s]));
  end;

var
  I: integer;
begin
  if FEmittedSymbols.IsExists(T) then
    Exit;
  case T.TypeCode of
    typClass:
    begin
      EmitRtti_Class(TClassType(T));
      for I := 0 to TClassType(T).Symbols.Count - 1 do
        EmitSymbolDecl(TClassType(T).Symbols[I]);
      FEmittedSymbols.Add(T, nil);
      if Assigned(TClassType(T).Base) then
        AddExternalSymbol(TClassType(T).Base);
    end;
    typRecord:
    begin
      EmitStructTypeDecl(T);
      EmitRtti_Record(TRecordType(T));
      for I := 0 to TRecordType(T).Symbols.Count - 1 do
        EmitSymbolDecl(TRecordType(T).Symbols[I]);
      FEmittedSymbols.Add(T, nil);
    end;
    typObject:
    begin
      EmitStructTypeDecl(T);
      EmitRtti_Object(TObjectType(T));
      for I := 0 to TObjectType(T).Symbols.Count - 1 do
        EmitSymbolDecl(TObjectType(T).Symbols[I]);
      FEmittedSymbols.Add(T, nil);
      if Assigned(TObjectType(T).Base) then
        AddExternalSymbol(TObjectType(T).Base);
    end;
    typInterface:
    begin
      EmitRtti_Intf(TInterfaceType(T));
      FEmittedSymbols.Add(T, nil);
    end;
    typProcedural:
    begin
      EmitProcTypeDecl(TProceduralType(T));
      FEmittedSymbols.Add(T, nil);
    end;
    typArray:
    begin
      EmitArrayTypeDecl(TArrayType(T));
      FEmittedSymbols.Add(T, nil);
    end;
  end;
end;

procedure TCodeGen.EmitVarUninit(Func: TFunction);

  function CleanupRoutine(T: TType): TSystemRoutine;
  begin
    Result := srTrunc;
    case T.TypeCode of
      typString: case TStringType(T).Kind of
          strAnsi: Result := srAStrClr;
          strWide: Result := srWStrClr;
          strUnicode: Result := srUStrClr;
          else
            Assert(False, 'CleanupRoutine');
        end;
      typInterface: Result := srIntfClr;
      typVariant: Result := srVarClr;
      else
        Assert(False, 'CleanupRoutine');
    end;
  end;

  procedure LocalFree(const Name: string; T: TType; Ref: TSymbol);
  var
    ty, s: string;
    Va: TVarInfo;
  begin
    VarInfoInit(Va);
    ty := TypeStr(T);
    case T.TypeCode
      of
      typString: if TStringType(T).Kind in [strAnsi, strWide, strUnicode] then
        begin
          Self.EmitOp_LoadRef(Ref, Va);
          if TStringType(T).Kind = strAnsi then
            ty := 'i8**'
          else
            ty := 'i16**';
          EmitCallSys(CleanupRoutine(T), [ty], [Va.Name]);
        end;
      typInterface, typVariant:
      begin
        Self.EmitOp_LoadRef(Ref, Va);
        s := TempVar;
        WriteCode('%s = bitcast %s* %s to i8*', [s, ty, Name]);
        EmitCallSys(CleanupRoutine(T), ['i8*'], [s]);
      end;
      typDynamicArray:
      begin
        Self.EmitOp_LoadRef(Ref, Va);
        s := TempVar;
        WriteCode('%s = bitcast %s* %s to i8*', [s, ty, Name]);
        WriteCode('call %s void @System._DynArrayClear(i8* %s, i8* bitcast(%%%s.$init.t* @%s.$init to i8*))',
          [DefCC, s, T.Name, T.Name]);
      end;
      typRecord: if staNeedInit in TRecordType(T).RecordAttr then
        begin
          Self.EmitOp_LoadRef(Ref, Va);
          s := TempVar;
          WriteCode('%s = bitcast %s* %s to i8*', [s, ty, Name]);
          WriteCode('call %s void @System._RecordFree(i8* %s, i8* bitcast(%%%s.$init.t* @%s.$init to i8*))',
            [DefCC, s, T.Name, T.Name]);
        end;
      typArray: if staNeedInit in TArrayType(T).ArrayAttr then
        begin
        end;
    end;
  end;

  procedure ArgFree(Arg: TFuncParam);
  begin
    if not (saUsed in Arg.Attr) then
      Exit;
    if not (asNeedFree in Arg.States) then
      Exit;
    LocalFree(Arg.Name, Arg.ParamType, Arg);
  end;

  procedure VarFree(V: TVariable);
  begin
    if not (vaLocal in V.VarAttr) then
      Exit;
    if not (vsNeedFree in V.States) then
      Exit;
    LocalFree(V.Name, V.VarType, V);
  end;

var
  List: TFPList;
  I: integer;
  Sym: TSymbol;
begin
  List := TCode(Func.Codes).Vars;
  for I := 0 to List.Count - 1 do
  begin
    Sym := TSymbol(List[i]);
    case Sym.NodeKind of
      nkVariable: VarFree(TVariable(Sym));
      nkFuncParam: ArgFree(TFuncParam(Sym));
    end;
  end;
end;

procedure TCodeGen.EnterLandingpad(const LPad: string);
begin
  with FCurCntx do
  begin
    LandingpadStack.Add(LPad);
  end;
end;

procedure TCodeGen.EnterLandingpad(Handler: TCmd);
var
  LPad, LPrev: string;
  //i: Integer;
begin
  with FCurCntx do
  begin
    if LandingpadStack.Count > 0 then
      LPrev := LandingpadStack[LandingpadStack.Count - 1]
    else
      LPrev := '';
  end;
  Inc(FCurCntx.PadID);
  case Handler.Kind of
    insCleanup:
    begin
      LPad := Format('clean.lpad%d', [FCurCntx.PadID]);
      TCleanupCmd(Handler).OutterLPad := LPrev;
    end;
    insHandleExcept:
    begin
      LPad := Format('except.lpad%d', [FCurCntx.PadID]);
      THandleExceptCmd(Handler).OutterLPad := LPrev;
    end;
    insHandleCtorExcept: LPad := 'ctor.lpad';
    insHandleScExcept: LPad := 'sc.lpad';
    else
      Assert(False, 'EnterLandingpad');
  end;
  with FCurCntx do
  begin
    Landingpads.AddObject(LPad, Handler);
    LandingpadStack.AddObject(LPad, Handler);
  end;
end;

function TCodeGen.FuncDecl(F: TFunctionDecl; NeedArgName: boolean; const Name: string): string;
var
  i: integer;
  s, ret, n, attr: string;
  Arg: TFuncParam;
  retConvert, isSafecall, isCtor, isDtor, isMeth: boolean;
  cc: TCallingConvention;
  parentCntx: TEmitFuncContext;
begin
  isMeth := (F.NodeKind = nkMethod) and not (saStatic in F.Attr);
  isCtor := (F.NodeKind = nkMethod) and (TMethod(F).MethodKind = mkConstructor);
  isDtor := (F.NodeKind = nkMethod) and (TMethod(F).MethodKind = mkDestructor);
  isSafecall := F.CallConvention = ccSafeCall;
  retConvert := not isCtor and not isDtor and (F.ReturnType <> nil) and (IsSpecialType(F.ReturnType) or isSafecall);
  s := '';
  if isMeth then
  begin
    if NeedArgName then
    begin
      if isCtor then
        s := 'i8* %.vmt, '
      else
        s := 'i8* %Self, ';
    end
    else
      s := 'i8*, ';
    if isCtor then
      case TMethod(F).ObjectKind of
        okObject: if NeedArgName then
            s := s + '%SizeInt %.vmt, '
          else
            s := s + '%SizeInt, ';
        okRecord, okClass: if NeedArgName then
            s := s + 'i8 %.flag, '
          else
            s := s + 'i8, ';
      end;
    if isDtor then
      if NeedArgName then
        s := s + 'i8 %.outterMost, '
      else
        s := s + 'i8, ';
  end
  else if TFunction(F).Level > 0 then
  begin
    parentCntx := TEmitFuncContext(FCntxList[TFunction(F).Level - 1]);
    s := Format('%s* %%.fp%d, ', [parentCntx.FrameTyStr, parentCntx.Level]);
  end;
  for i := 0 to F.ParamCount - 1 do
  begin
    arg := F.Params[i];
    s := s + ArgDeclStr(arg, NeedArgName);
    if (Arg.ParamType.TypeCode = typOpenArray) then
    begin
      s := s + ', %SizeInt';
      if NeedArgName then
        s := s + Format(' %%%s.high, ', [arg.Name]);
    end
    else
      s := s + ', ';
  end;
  if retConvert then
    s := s + TypeStr(F.ReturnType) + '* %Result.addr'
  else if fmVarargs in F.Modifiers then
    s := s + '...'
  else if s <> '' then
    Delete(s, Length(s) - 1, 2);
  if isSafecall then
    ret := 'i32'
  else if (F.ReturnType = nil) or retConvert then
    ret := 'void'
  else
    ret := TypeStr(F.ReturnType);
  if Name = '' then
    n := MangledName(F)
  else
    n := Name;
  if fmNoReturn in F.Modifiers then
    attr := 'noreturn'
  else
    attr := '';
  if isSafecall then
    cc := ccStdCall
  else
    cc := F.CallConvention;
  Result := Format('%s %s @%s(%s)%s', [CCStr(cc), ret, n, s, attr]);
end;

function TCodeGen.GetIR: string;
begin
  Result := FExtDecls.Text + #13#10;
  Result := Result + FDecls.Text + #13#10;
  Result := Result + FCodes.Text;
end;

function TCodeGen.IsRangeCheckNeeded(RT, LT: TType): boolean;
begin
  Result := False;
  if LT.TypeCode = typSubrange then
  begin
    if RT.TypeCode = typSubrange then
      if TSubrangeType(RT).SubSetOf(TSubrangeType(LT)) then
        Exit;
  end
  else if (LT.IsBoolean) or (RT.TypeCode = LT.TypeCode) or (LT.Size > RT.Size) then
    Exit;
  Result := True;
end;

function TCodeGen.LabelStr(const Prefix: string): string;
begin
  Inc(FCurCntx.LabelID);
  Result := Prefix + IntToStr(FCurCntx.LabelID);
end;

procedure TCodeGen.LeaveLandingpad;
begin
  with FCurCntx.LandingPadStack do
    if Count > 0 then
      Delete(Count - 1);
end;

function TCodeGen.ProcTypeStr(T: TProceduralType; const Name: string): string;
var
  i: integer;
  s, ret: string;
  arg: TFuncParam;
  convResult, isSafecall: boolean;
begin
  isSafecall := T.CallConvention = ccSafeCall;
  convResult := (T.MethodKind = mkNormal) and (T.ReturnType <> nil) and (IsSpecialType(T.ReturnType) or isSafecall);
  s := '';
  if T.IsMethodPointer then
  begin
    s := 'i8*, ';
    if T.MethodKind = mkConstructor then
      case T.ObjectKind of
        okObject: s := s + '%SizeInt, ';
        okRecord, okClass: s := s + 'i8, ';
      end;
    if T.MethodKind = mkDestructor then
      s := s + 'i8, ';
  end;
  for i := 0 to T.ParamCount - 1 do
  begin
    arg := T.Params[i];
    s := s + ArgTypeStr(arg.ParamType, arg.Modifier) + ', ';
    if Assigned(arg.ParamType) and (arg.ParamType.TypeCode = typOpenArray) then
      s := s + '%%SizeInt, ';
  end;
  if convResult then
    s := s + TypeStr(T.ReturnType) + '*'
  else if s <> '' then
    Delete(s, Length(s) - 1, 2);
  if isSafecall then
    ret := 'i32'
  else if (T.ReturnType = nil) or convResult then
    ret := 'void'
  else
    ret := TypeStr(T.ReturnType);
  if Name <> '' then
    Result := Format('%%%s = type %s (%s)*', [Name, ret, s])
  else
    Result := Format('%s (%s)*', [ret, s]);
end;

function TCodeGen.TempVar: string;
begin
  Inc(FCurCntx.TempID);
  Result := '%.' + IntToStr(FCurCntx.TempID);
end;

function TCodeGen.TypeStr(Typ: TType): string;

  function NameStr(T: TType): string;
  begin
    EmitTypeDecl(T);
    Result := '%' + MangledName(T);
  end;

  function RecordTypeStr(T: TRecordType): string;
  begin
    if T.Name <> '' then
      Result := NameStr(T)
    else
      Result := Format('[%d x i8]', [int64(T.Size)]);
  end;

  function RefTypeStr(T: TType): string;
  begin
    Result := '%' + MangledName(T) + '*';
  end;

  function OpenArrayTypeStr(T: TOpenArrayType): string;
  begin
    if T.ElementCount <> 0 then
    begin
      if T.ElementType.TypeCode <> typUntype then
        Result := Format('[%d x %s]', [T.ElementCount, TypeStr(T.ElementType)])
      else
        Result := Format('[%d x %%SizeInt]', [T.ElementCount * 2]);
    end
    else
    begin
      if T.ElementType.TypeCode <> typUntype then
        Result := TypeStr(T.ElementType) + '*'
      else
        Result := '%System.TVarRec*';
    end;
  end;

  function StrTypeStr(T: TStringType): string;
  begin
    case T.Kind of
      strAnsi: Result := 'i8*';
      strWide, strUnicode: Result := 'i16*';
      strAShort: Result := Format('[%d x i8]', [T.CharCount + 2]);
      strWShort: Result := Format('[%d x i16]', [T.CharCount + 2]);
      else
        Assert(False, 'StrTypeStr');
    end;
  end;

  function SetStr(T: TSetType): string;
  begin
    if T.Size = 1 then
      Result := 'i8'
    else if T.Size = 2 then
      Result := 'i16'
    else
    if T.Size = 4 then
      Result := 'i32'
    else
      Result := Format('[%d x i8]', [T.Size]);
  end;

  function PointerStr(T: TPointerType): string;
  begin
    if T.RefType = nil then
      Result := 'i8*'
    else
      Result := TypeStr(T.RefType) + '*';
  end;

  function ArrayTypeStr(T: TArrayType): string;
  var
    Size: int64;
  begin
    Size := T.Range.RangeEnd - T.Range.RangeBegin + 1;
    Result := Format('[%d x %s]', [Size, TypeStr(T.ElementType)]);
  end;

  function EnumStr(T: TEnumType): string;
  begin
    if T.Size = 1 then
      Result := 'i8'
    else if T.Size = 2 then
      Result := 'i16'
    else
      Result := 'i32';
  end;

begin
  case Typ.TypeCode of
    typUntype: Result := 'i8';
    typInt: Result := typIntMaps[TIntType(Typ).Kind];
    typNumeric: Result := typNumericMaps[TNumericType(Typ).Kind];
    typBool: Result := typBoolMaps[TBoolType(Typ).Kind];
    typChar: Result := typCharMaps[TCharType(Typ).Kind];
    typPAnsiChar: Result := 'i8*';
    typPWideChar: Result := 'i16*';
    typString: Result := StrTypeStr(TStringType(Typ));
    typSubrange: Result := TypeStr(TSubrangeType(Typ).BaseType);
    typDynamicArray: Result := TypeStr(TDynamicArrayType(Typ).ElementType) + '*';
    typRecord: Result := RecordTypeStr(TRecordType(Typ));
    typObject: Result := NameStr(typ);
    typArray: Result := ArrayTypeStr(TArrayType(typ));
    typPointer: Result := PointerStr(TPointerType(typ));
    typProcedural: if typ.IsMethodPointer then
        Result := '[2 x i8*]'
      else if typ.Name = '' then
        Result := Self.ProcTypeStr(TProceduralType(typ))
      else
        Result := NameStr(typ);
    typSet: Result := SetStr(TSetType(typ));
    typEnum: Result := EnumStr(TEnumType(typ));
    typAlias, typClonedType: Result := TypeStr(Typ.NormalType);
    typSymbol: Assert(False, 'TypeStr');
    typOpenArray: Result := OpenArrayTypeStr(TOpenArrayType(Typ));
    else
      Result := typMaps[Typ.TypeCode];
  end;
end;

function TCodeGen.WriteCode(const S: string): integer;
begin
  Result := FCodes.Add(#9 + S);
end;

function TCodeGen.WriteCode(const S: string; const Args: array of const): integer;
begin
  Result := FCodes.Add(#9 + Format(S, Args));
end;

function TCodeGen.WriteCodeNI(const s: string): integer;
begin
  Result := FCodes.Add(s);
end;

procedure TCodeGen.WriteDecl(const S: string);
begin
  FDecls.Add(S);
end;

procedure TCodeGen.WriteDecl(const S: string; const Args: array of const);
begin
  FDecls.Add(Format(S, Args));
end;

function TCodeGen.WriteLabel(const S: string): integer;
begin
  Result := FCodes.Add(S + ':');
  FCurLabel := S;
end;

constructor TEmitFuncContext.Create;
begin
  Codes := TStringList.Create;
  Landingpads := TStringList.Create;
  LandingpadStack := TStringList.Create;
end;

destructor TEmitFuncContext.Destroy;
begin
  Codes.Free;
  Landingpads.Free;
  LandingpadStack.Free;
  inherited;
end;

end.
