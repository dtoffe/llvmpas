unit parser;

{$IFDEF FPC}
{$MODE delphi}
{$H+}{$J-}
{$ENDIF}

interface

uses Classes, SysUtils, lex, ast, cntx, hashtable;

{
need to add:
1. StrictImplicitCast strict implicit conversion (conversion between various ints,
     And assigning untyped pointers to typed pointers and class, classref, dynamicarray)
2. The initial value of local variables
3. inline
4. Combine constants in CheckExpr (completed)
5. Improve with statement: a with statement can carry multiple identification lists,
     The latter identifier can be a member of the previous identifier.
}

const
  MAX_UNGET = 7;

type
  TParseState = (psInIntfSect, psInImplSect, psInClass, psInRecord, psInObject, psInIntf,
    psInDispIntf, psInFunc, psInType, psInVar,
    psInField, psInAccessor, psInPacked, psInLeftVal, psInClassPrefix, psInWhileStmt, psInForStmt,
    psInForEachStmt, psInRepeatStmt, psInFuncBody,
    psInTypeExpr, // currently in type expression
    psInConstExpr, // The current semantics requires a constant expression.
    psNotAllowAddr, psStopOnErr);
  TParseStates = set of TParseState;

  TParseStateInfo = record
    State: TParseState;
    IsSet: boolean;
  end;

  TFunctionHeader = class
  public
    Name: string;
    Names: array of string;
    CountOfNames: integer;
    FileName, RoutineName, ImplementingName: string;
    RoutineNo: integer;
    MsgNo: integer;
    DispID: integer;
    ReturnType: TType;
    Params: TFuncParamList;
    PrevDecl: TFunctionDecl;
    Directives: TDirectiveIdents;
    Modifiers: TFunctionModifiers;
    CallConvention: TCallingConvention;
    Hints: TMemberHints;
    MethodKind: TMethodKind;
    ObjectKind: TObjectKind;
    ClassPrefix: boolean;
    constructor Create;
    destructor Destroy; override;
    procedure Reset;
  end;

  TQualifiedID = class
  public
    Name: string;
    Names: array of TSymString;
    CountOfNames: integer;
    constructor Create;
    procedure Reset;
    function Id: string;
    function SameScope(const Scopes: array of string): boolean;
  end;

  PTokenInfo = ^TTokenInfo;

  TTokenInfo = record
    TokenStr: string;
    Token: TToken;
    Coord: TAstNodeCoord;
  end;
  TSyntaxOption = (synProcvarFpc);
  TSyntaxOptions = set of TSyntaxOption;

  TParser = class
  private
    FOnError: TParserErrorEvent;
    FScanner: TScanner;
    FCurToken: TToken;
    FCurTokenString: string;
    FExternSymbols: TSymbolTable;
    FDefinedSymbols: THashTable;
    FScopeList: TFPList;
    FWithList: TFPList;
    FCurOverloadFunc: TFunctionDecl;
    FCurSymbolPos: TSymbolPosition;
    // In the non-public part: implementation section such as program or unit
    FInternalSection: boolean;
    FSyntaxOptions: TSyntaxOptions;
    // UngetToken support:
    FTokenBuffer: array[0..MAX_UNGET] of TTokenInfo;
    FTokenIndex, FTokenHead: smallint;
    FCurVisibility: TMemberVisibility;
    FHeader: TFunctionHeader;
    FQId: TQualifiedId;
    FTemp: string;
    FTempValue: TValueRec;
    property Scanner: TScanner read FScanner;
    property CurToken: TToken read FCurToken;
    property CurTokenString: string read FCurTokenString;
    procedure NextToken;
    procedure UngetToken(Step: integer = 1);
    procedure Expect(T: TToken; Stop: boolean = True);
    procedure OnScannerError(const Msg: string; Stop: boolean);
    procedure OnScannerDirective(var dinfo: TDirectiveInfo);
    procedure OnScannerIfDefined(const S: string; out IsDefined: boolean);
    procedure OnScannerIfOpt(C: char; out IsSet: boolean);
    procedure OnScannerIfEval(out IsDefined: boolean);
    procedure InitAstNode(ANode: TAstNode);
    procedure InitExpr(Expr: TExpr);
    // Add a symbol of a unit to the ExternSymbols list
    procedure AddSymbols(M: TModule);
    // Add to the symbol table of the current Scope
    function AddSymbol(Sym: TSymbol): boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    // current symbol table
    function CurSymbols: TSymbolTable;
    procedure EnterScope(SymTable: TSymbolTable); overload;
    procedure LeaveScope;
    procedure ClearScopes;
    procedure EnterWithStmt(Sym: TSymbolExpr);
    procedure LeaveWithStmt;
    procedure ClearWithList;
    function ParseTypeExpr: TExpr;
    function ParseExpr: TExpr;
    function ParseAddExpr: TExpr;
    function ParseMulExpr: TExpr;
    function ParseFactor: TExpr;
    function ParseDesignator: TExpr;
    function ParseLiteral: TExpr;
    function ParseSetConstructor: TExpr;
    function ParseSetElementList: TExpr;
    function ParseExprList: TExpr;
    function SimplifyQualId: TExpr;
    // Analyze the full name of the type such as System.TObject
    function ParseTypeRef: TType;
    // Analyze fully qualified IDs such as System.TObject, and store the results in FQID
    procedure ParseQualifiedId(const First: string = '');
    // Analyze the fully qualified ID and find the actual TSymbol: TType or TConstant
    function ParseQualifiedSym(const First: string = ''): TSymbol;
    function ParseStatement(Parent: TStatement): TStatement;
    function ParseCompoundStmt: TCompoundStmt;
    function ParseSimpleStmt: TStatement;
    function ParseLabeledStmt(const S: string): TStatement;
    function ParseIfStmt: TIfStmt;
    function ParseWhileStmt: TWhileStmt;
    function ParseForStmt: TForStmt;
    function ParseGotoStmt: TGotoStmt;
    function ParseRepeatStmt: TRepeatStmt;
    function ParseWithStmt(Parent: TStatement): TCompoundStmt;
    function ParseStmtList(Parent: TStatement; EndTokens: TTokens): TCompoundStmt;
    function ParseRaiseStmt: TRaiseStmt;
    function ParseTryStmt: TTryStmt;
    function ParseCaseStmt: TCaseStmt;
    function ParseFunction(Parent: TSymbol): TSymbol;
    procedure ParseFunctionDirective(Result: TFunctionHeader);
    procedure ParseFunctionHeader(Result: TFunctionHeader); overload;
    procedure ParseFunctionBlock(Func: TFunction);
    procedure CheckFunction(F: TFunction);
    function CheckOverloads(ExistsFunc, Func: TFunctionDecl): boolean;
    procedure ParseFuncParamList(Parent: TSymbol; Params: TFuncParamList);
    function ParseIdList(SymClass: TSymbolClass): TSymbol;
    function ParseHints: TMemberHints;
    procedure ParseBlock(Parent: TSymbol);
    procedure ParseUsesClause;
    procedure ParseInterfaceSection;
    procedure ParseImplementSection;
    procedure ParseTypeSection(Parent: TSymbol);
    function ParseTypeDecl(const TypName: string = ''; Parent: TSymbol = nil): TType;
    function ParseClassType(const TypName: string; Parent: TSymbol; out NotAddSym: boolean): TClassType;
    function ParseClassRefType: TClassRefType;
    function ParseProperty(Parent: TType; IsStatic: boolean): TProperty;
    function ParseIntfProperty(Parent: TType): TIntfProperty;
    function ParseField(FieldClass: TSymbolClass): TField;
    function ParseRecordType(const TypName: string; Parent: TSymbol): TRecordType;
    function ParseInterfaceType(const IntfName: string; Parent: TSymbol; out NotAddSym: boolean): TInterfaceType;
    function ParseObjectType(const ObjName: string): TObjectType;
    procedure ParseVarSection(Parent: TSymbol);
    procedure ParseConstSection(Parent: TSymbol);
    // Analyze simple constant values (non-array, record)
    // If there is a constant expression at the current position, and the analysis and evaluation are successful,
    // It returns TRUE, and Value and ValTyp store constant values and actual types
    // Otherwise, the value of Value is not changed, but ValTyp still stores the type of the actual expression
    function ParseConstSimpleValue(Typ: TType; var Value: TValueRec; out ValTyp: TType): boolean;
    procedure ParseConstArray(Typ: TArrayType; var V: TValueRec);
    procedure ParseConstRecord(Typ: TRecordType; var V: TValueRec);
    procedure ParseLabelSection(Parent: TSymbol);
    procedure ParseResStringSection(Parent: TSymbol);
    // Check if Value exceeds the definition of typ, return True, indicating that Value has exceeded
    // Return False, indicating that it is not exceeded or does not need to be checked
    // Strict: Indicates whether to perform strict inspection. If you check enum or subrange,
    // Strict inspection will check the minimum and maximum values of the type, on the contrary, only check the value that the size of the type can hold
    function IsConstantOutOfRange(typ: TType; const Value: TValueRec; Strict: boolean = False): boolean; overload;
    function IsConstantOutOfRange(typ: TType; Value: int64; Strict: boolean = False): boolean; overload;
    // Check Expr, if Expr is invalid or the type is not bool, an error is issued
    function CheckBoolExpr(var Expr: TExpr): boolean;
    function IsSameArgs(L1, L2: TFuncParamList): boolean;
    procedure CheckForward;
    function ParseStrExpr(const DefValue: string): string;
    function ParseIntExpr(const DefValue: integer = 0): integer;
  private
    FErrorCount: integer;
    FMaxErrorCount: integer;
    FContext: TCompileContext;
    FModule: TModule; // current module
    FTopFunction: TFunction; // The topmost function currently being analyzed
    FCurFunction: TFunction; // The function currently being analyzed
    // The superior symbol of the current position, such as the type segment being analyzed, FCurParent may be TMoudle, or TClassType
    // If the analysis function, FCurParent is FModule,
    // If the method is analyzed, FCurParent is the class/interface/object where the method is located
    // If the type, var, const, FCurParent under the analysis function/method is the TFunction/TMethod
    FCurParent: TSymbol;
    FCurStates: TParseStates;
    FExpectedProcType: boolean;
    // compile switch
    FMinEnumSize: Byte; // 1, 2, 4
    FAlignSize: Byte;   // 1, 2, 4, 8, 16
    FPointerSize: Byte; // 4, 8
    FRttiInfo: Boolean;     // $M+
    FTypedAddress: Boolean; // $T+
    FWriteableConst: Boolean; // $J+
    FCodeSwitches: TCodeSwitches;
    function GetSetType(typ: TSubrangeType): TSetType; overload;
    function GetSetType(typ: TEnumType): TSetType; overload;
    function GetSubrangeType(typ: TEnumType): TSubrangeType;
    function GetOpenArrayType(const typ: TType): TOpenArrayType;
    // Take the overloaded list of the function
    procedure GetOverloadBegin(Func: TFunctionDecl);
    function GetOverloadNext: TFunctionDecl;
    procedure GetOverloadEnd;
    procedure StateSet(State: TParseState; out StateInfo: TParseStateInfo);
    procedure StateClear(State: TParseState; out StateInfo: TParseStateInfo);
    procedure StateRestore(const StateInfo: TParseStateInfo);
    function CreateElement(SymClass: TSymbolClass): TSymbol;
    function CreateType(TypClass: TTypeClass): TType;
    function CreateBinaryExpr(op: TExprOpCode; L: TExpr = nil; R: TExpr = nil): TBinaryExpr;
    function CreateUnaryExpr(op: TExprOpCode; Operand: TExpr = nil): TUnaryExpr;
    function CreateListExpr: TListExpr;
    function CreateConstExpr(typ: TExprOpCode): TConstExpr;
    function CreateSymbolExpr(const Name: string = ''): TSymbolExpr;
    procedure ReleaseExpr(E: TExpr);
    function CreateStmt(Stmt: TStatementClass): TStatement;
    function FindSymbol(const S: string): TSymbol; overload;
    {function FindSymbol(M: TModule; const S: string): TSymbol; overload;}
    function FindSymbol(Typ: TType; const S: string): TSymbol; overload;
    function FindWith(const S: string; out Sym: TSymbolExpr; out Elem: TSymbol): boolean;
    // Determine whether Referred can be accessed from Ref
    function IsVisible(Ref, Referred: TSymbol): boolean;
  public
    FIsSystemUnit: boolean; // Whether to compile System unit
    procedure InternalError(const Msg: string);
    procedure ParseError(const Msg: string; Stop: boolean = False); overload;
    procedure ParseError(const Msg: string; Args: array of const; Stop: boolean = False); overload;
    procedure ParseError(const Coord: TAstNodeCoord; const Msg: string; Stop: boolean = False); overload;
    procedure ParseError(const Coord: TAstNodeCoord; const Msg: string; Args: array of const;
      Stop: boolean = False); overload;
    procedure DoWarning(const Coord: TAstNodeCoord; const Msg: string; Args: array of const); overload;
    procedure DoWarning(const Coord: TAstNodeCoord; const Msg: string); overload;
    procedure DoHint(const Coord: TAstNodeCoord; const Msg: string; Args: array of const); overload;
    procedure DoHint(const Coord: TAstNodeCoord; const Msg: string); overload;
    // Check if R can be assigned to L
    // AdjustRT indicates whether to change the Typ of R, AdjustRT=true, and replace the Typ of R when CanAssign returns True
    function CanAssign(LT: TType; R: TExpr; AdjustRT: boolean = True): boolean;
    // Check whether T2 can be assigned to T1
    function CheckAssignCompatibility(T1, T2: TType): boolean; overload;
  public
    procedure FindProper(E: TUnaryExpr; ProcType: TProceduralType);
    function CheckExpr(var Expr: TExpr): boolean;
    // Try to evaluate opNE..opSHR, opNot..opPos, opCast, opAddr, opCALL, opSET
    function TryEvalConst(E: TExpr; out Value: TValueRec): boolean;
    // Try to get a value. E is opCONST, opNIL, opSymbol
    function TryEvalGet(E: TExpr; var Value: TValueRec): boolean;
    function ParseConstExpr: TExpr;
    function CheckConstExpr(var E: TExpr): boolean;
    constructor Create(AContext: TCompileContext);
    destructor Destroy; override;
    procedure OpenCode(const S: string);
    procedure OpenFile(const FileName: string);
    function Parse: TModule;
    //    procedure ParseModule(M: TModule);
    function ParseProgram: TModule;
    function ParseUnit: TModule;
    procedure ParseUnitInterface(M: TModule);
    procedure ParseUnitImplementation;
    property ErrorCount: integer read FErrorCount;
    property OnError: TParserErrorEvent read FOnError write FOnError;
  end;

implementation

uses err, func;

type
  TPropDirective = (idNon, idRead, idWrite, idIndex, idDefault, idStored, idNoDefault, idReadOnly,
    idWriteOnly, idDispID);

function ParsePropDirective(const S: string): TPropDirective;
begin
  Result := idNon;
  if Length(S) < 4 then   // min 'read'
    Exit;
  case S[1] of
    'R', 'r': if SameText(S, 'read') then
        Result := idRead
      else if SameText(S, 'readonly') then
        Result := idReadOnly;
    'W', 'w': if SameText(S, 'write') then
        Result := idWrite
      else if SameText(S, 'writeonly') then
        Result := idWriteOnly;
    'I', 'i': if SameText(S, 'index') then
        Result := idIndex;
    'D', 'd': if SameText(S, 'default') then
        Result := idDefault
      else if SameText(S, 'dispid') then
        Result := idDispId;
    'S', 's': if SameText(S, 'stored') then
        Result := idStored;
    'N', 'n': if SameText(S, 'nodefault') then
        Result :=
          idNoDefault;
  end;
end;

function IsCallConv(const S: string; out cc: TCallingConvention): boolean;
begin
  Result := True;
  if SameText(S, 'stdcall') then
    cc := ccStdCall
  else if SameText(S, 'register') then
    cc := ccRegister
  else if SameText(S, 'pascal') then
    cc := ccPascal
  else if SameText(S, 'safecall') then
    cc := ccSafeCall
  else if SameText(S, 'cdecl') then
    cc :=
      ccCDecl
  else
    Result := False;
end;

function IsModifier(const S: string; out M: TFunctionModifier): boolean;
const
  ModifierStr: array[fmVirtual..fmNoreturn] of string =
    ('virtual', 'dynamic', 'abstract', 'override', 'overload', 'message', 'reintroduce', 'static',
    'inline', 'assembler', 'varargs', 'local', 'dispid', 'export', 'near', 'far', 'external', 'forward', 'noreturn');
var
  I: TFunctionModifier;
begin
  for I := Low(ModifierStr) to High(ModifierStr) do
    if SameText(S, ModifierStr[I]) then
    begin
      M := I;
      Result := True;
      Exit;
    end;
  Result := False;
end;

function IsHint(const S: string; var H: TMemberHint): boolean;
begin
  // hDeprecated, hLibrary, hPlatform, hExperimental, hUnimplemented
  Result := True;
  if SameText(S, 'deprecated') then
    H := hDeprecated
  else if SameText(S, 'library') then
    H := hLibrary
  else if SameText(S, 'platform') then
    H := hPlatform
  else if SameText(S, 'experimental') then
    H := hExperimental
  else if SameText(S, 'unimplemented') then
    H := hUnimplemented
  else
    Result := False;
end;

function TParser.AddSymbol(Sym: TSymbol): boolean;
begin
  Result := CurSymbols.Add(Sym);
  if Result then
    ParseError(Sym.Coord, SErr_RedeclaredIdent, [Sym.Name]);
end;

procedure TParser.AddSymbols(M: TModule);
{  procedure Add(List: TList);
  var
    I: Integer;
  begin
    for I := 0 to List.Count - 1 do
      FExternSymbols.Add(TSymbol(List[I]));
  end;}
var
  I: integer;
begin
  // AutoAddToOwner temporarily handle it like this
  CurSymbols.AutoAddToOwner := False;
  AddSymbol(M);
  CurSymbols.AutoAddToOwner := True;
  // The symbols in all uses units are added to a symbol table to increase the search speed
  FExternSymbols.EnsureCapacity(M.Symbols.Count);
  for I := 0 to M.Symbols.Count - 1 do
    FExternSymbols.Add(M.Symbols[I]);
  {  Add(M.InterfaceSection.Types);
  Add(M.InterfaceSection.ResStrings);
  Add(M.InterfaceSection.Constants);
  Add(M.InterfaceSection.Variables);
  Add(M.InterfaceSection.Functions);
  Add(M.InterfaceSection.BuiltinFuncs);
  Add(M.InterfaceSection.ThreadVars);}
end;

function TParser.CanAssign(LT: TType; R: TExpr; AdjustRT: boolean): boolean;
begin
  if (LT.TypeCode = typClassRef) and (R.Typ.TypeCode = typClass) then
  begin
    Result := R.IsTypeSymbol;
    if Result and AdjustRT then
      R.Typ := LT;
  end
  else if (LT.TypeCode = typClass) and (R.Typ.TypeCode = typClass) and R.IsCtorCall then
  begin
    // Consider this situation, a class without a constructor uses the constructor of the base class:
    // type tmyobj = class end;
    // var obj: tmyobj;
    // obj := tmyobj.create;
    Result := TClassType(LT).IsInheritedFrom(TClassType(R.Typ));
    if Result and AdjustRT then
      R.Typ := LT;
  end
  else if R.IsNilConst then
  begin
    Result := LT.TypeCode in [typPointer, typProcedural, typClass, typClassRef, typPAnsiChar,
      typPWideChar, typDynamicArray, typInterface];
    // ??Why don't changed
    //if Result and AdjustRT then R.Typ := LT;
  end
  else if R.IsStringConstant then
  begin
    // case: R is string constant, L is PAnsiChar,PWideChar,PackedString
    Result := LT.IsStringArithCompatible;
    if Result and AdjustRT and (LT.TypeCode <> typVariant) and (LT.TypeCode <> typArray) then
    begin
      R.Typ := LT;
    end;
  end
  else
    Result := CheckAssignCompatibility(LT, R.Typ);
end;

function TParser.CheckAssignCompatibility(T1, T2: TType): boolean;

  function InterfaceCompatible(T1, T2: TInterfaceType): boolean;
  begin
    // IDispatch is compatible with disinterface
    // Inherited from IDispatch is not compatible with disinterface
    if T1.IsDisp then
      Result := T1 = T2
    else
    begin
      Result := T1 = T2;
      if not Result then
        Result := (T2.IsDisp and (T1 = FContext.FIDispatchType)) or (T1.IsInheritedFrom(T2));
    end;
  end;

  function IsSameProcType(P1, P2: TProceduralType): boolean;
  begin
    Result := (P1.ReturnType = P2.ReturnType) and (P1.CallConvention = P2.CallConvention) and
      (P1.IsMethodPointer = P2.IsMethodPointer) and IsSameArgs(P1.Params, P2.Params);
  end;

  function CheckPointee(P1, P2: TPointerType): boolean;
  begin
    // todo 1: There may still be problems, such as PInteger and PLongint
    Result := (P1.RefType = P2.RefType) or ((P1.RefType.TypeCode = typObject) and
      (P2.RefType.TypeCode = typObject) and TObjectType(P2.RefType).IsInheritedFrom(TObjectType(P1.RefType)));
  end;

begin
  {
    T1 and T2 are of the same type, and it is not a file type or structured type that contains a file type at any level.
    T1 and T2 are compatible ordinal types.
    T1 and T2 are both real types.
    T1 is a real type and T2 is an integer type.
    T1 is PChar or any string type and the expression is a string constant.
    T1 and T2 are both string types.
    T1 is a string type and T2 is a Char or packed-string type.
    T1 is a long string and T2 is PChar.
    T1 and T2 are compatible packed-string types.
    T1 and T2 are compatible set types.
    T1 and T2 are compatible pointer types.
    T1 and T2 are both class, class-reference, or interface types and T2 is a derived from T1.
    T1 is an interface type and T2 is a class type that implements T1.
    T1 is PChar or PWideChar and T2 is a zero-based character array of the form array[0..n] of Char.
    T1 and T2 are compatible procedural types. (A function or procedure identifier is treated, in certain assignment statements, as an expression of a procedural type.
    See procedural types in statements and expressionson page 5-29.)
    T1 is Variant and T2 is an integer, real, string, character, Boolean, or interface type.
    T1 is an integer, real, string, character, or Boolean type and T2 is Variant.
    T1 is the IUnknown or IDispatch interface type and T2 is Variant. (The variant's type code must be varEmpty, varUnknown, or varDispatch if T1 is IUnknown, and varEmpty or varDispatch if T1 is IDispatch.)
    }
    //  if T1.TypeCode = typSubrange then T1 := TSubrangeType(T1).BaseType;
    //  if T2.TypeCode = typSubrange then T2 := TSubrangeType(T2).BaseType;
  T1 := T1.NormalType;
  T2 := T2.NormalType;
  case T1.TypeCode of
    typInt: Result := T2.TypeCode in [typInt, typVariant];
    typNumeric: Result := T2.TypeCode in [typInt, typNumeric, typVariant];
    typBool: Result := T2.TypeCode in [typBool, typVariant];
    typChar: Result := (T2.TypeCode = typVariant) or ((T2.TypeCode = typChar) and
        (TCharType(T2).Kind = TCharType(T1).Kind));
    typPointer: if TPointerType(T1).IsUntype then
        Result := T2.TypeCode in [typPAnsiChar, typPWideChar, typPointer, typClass, typClassRef]
      else if T2.TypeCode = typPointer then
      begin
        if T2.IsUntypePointer then
          Result := True
        else
          Result := CheckPointee(TPointerType(T1), TPointerType(T2));
      end
      else
        Result := False;
    typPAnsiChar: case T2.TypeCode of
        typPointer: Result := TPointerType(T2).IsUntype;
        typPAnsiChar: Result := True;
        else
          Result := False;
      end;
    typPWideChar: case T2.TypeCode of
        typPointer: Result := TPointerType(T2).IsUntype;
        typPWideChar: Result := True;
        else
          Result := False;
      end;
    typProcedural: case T2.TypeCode of
        typPointer: Result := True;
        typProcedural:
        begin
          Result := TProceduralType(T1).IsMethodPointer = TProceduralType(T2).IsMethodPointer;
          if Result {and FTypedAddress } then // In the $T+ state, need to check the parameter list
            Result := IsSameProcType(TProceduralType(T1), TProceduralType(T2));
        end;
        else
          Result := False;
      end;
    typVariant: Result := T2.IsVariantCompatible;
    typString: Result := T2.IsStringCompatible or (t2.TypeCode in [typPAnsiChar, typPWideChar, typChar, typVariant]);
    typEnum: Result := T1 = T2;
    typSet: case T2.TypeCode of
        typSet: Result := CheckAssignCompatibility(TSetType(T1).RangeType, TSetType(T2).RangeType);
        else
          Result := False;
      end;
    typDynamicArray: Result := T1 = T2;
    typRecord: Result := T1 = T2;
    typClass: case T2.TypeCode of
        typPointer: Result := TPointerType(T2).IsUntype;
        typInterface: Result := TClassType(T1).IsImplemented(TInterfaceType(T2));
        typClass: Result := (T1 = T2) or TClassType(T2).IsInheritedFrom(TClassType(T1));
        else
          Result := False;
      end;
    typClassRef: case T2.TypeCode of
        typPointer: Result := TPointerType(T2).IsUntype;
        typClass: Result := TClassType(T2).IsInheritedFrom(TClassRefType(T1).RefType);
        typClassRef: Result := TClassRefType(T2).IsInheritedFrom(TClassRefType(T1));
        else
          Result := False;
      end;
    typObject: case T2.TypeCode of
        typPointer: Result := TPointerType(T2).IsUntype;
        typObject: Result := (T1 = T2) or TObjectType(T2).IsInheritedFrom(TObjectType(T1));
        else
          Result := False;
      end;
    typInterface: if T2.TypeCode = typInterface then
        Result := InterfaceCompatible(TInterfaceType(T1), TInterfaceType(T2))
      else
        Result := False;
    else
      Result := False;
  end;
end;

function TParser.CheckBoolExpr(var Expr: TExpr): boolean;
begin
  Result := CheckExpr(Expr);
  if Result then
  begin
    Result := Expr.Typ.IsBoolean;
    if not Result then
      ParseError(Expr.Coord, SErr_ExpectBoolExpr);
  end;
end;

function TParser.CheckConstExpr(var E: TExpr): boolean;
var
  S1: TParseStateInfo;
begin
  StateSet(psInConstExpr, S1);
  Result := CheckExpr(E);
  if Result then
    Result := E.IsConstantValue;
  if not Result then
    ParseError(E.Coord, SErr_ExpectConstExpr, psStopOnErr in FCurStates);
  StateRestore(S1);
end;

procedure TParser.FindProper(E: TUnaryExpr; ProcType: TProceduralType);

  function IsProper(Func: TFunctionDecl): boolean;
  begin
    Result := ProcType.IsMethodPointer = ((Func.NodeKind = nkMethod) and not TMethod(Func).IsClassOrStatic);
    if Result then
      Result := ProcType.Equals(Func.ProceduralType);
  end;

  function CheckGroup(var Func: TFunctionDecl): boolean;
  begin
    while Func <> nil do
    begin
      if IsProper(Func) then
      begin
        Result := True;
        Exit;
      end;
      Func := Func.NextOverload;
    end;
    Result := False;
  end;

var
  Func, Old: TFunctionDecl;
begin
  if E.OpCode <> opADDR then
    Exit;
  Func := E.Operand.GetFunctionSymbol;
  if (Func = nil) or not Func.IsOverload then
    Exit;
  if (fmOverload in Func.Modifiers) and not (eaOverloadRestrict in E.Operand.Attr) then
  begin
    Old := Func;
    GetOverloadBegin(Func);
    while Func <> nil do
    begin
      if CheckGroup(Func) then
      begin
        E.Operand.SetReference(Func);
        E.Typ := Func.ProceduralType;
        E.Operand.Typ := E.Typ;
        Exit;
      end;
      Func := GetOverloadNext;
    end;
    GetOverloadEnd;
    ParseError(E.Coord, 'Can not choose a overloaded version for %s', [Old.Name]);
  end
  else if Func.NextOverload <> nil then
  begin
    Old := Func;
    if CheckGroup(Func) then
    begin
      E.Operand.SetReference(Func);
      E.Typ := Func.ProceduralType;
      E.Operand.Typ := E.Typ;
    end
    else
      ParseError(E.Coord, 'Can not choose a overloaded version for %s', [Old.Name]);
  end;
end;

// todo 1: directly exposed function symbols, either expanded to call or
// regarded as function pointers, should be prefixed with @

function TParser.CheckExpr(var Expr: TExpr): boolean;
  procedure CheckConst(E: TConstExpr); forward;

  procedure IncompatibleErr(const Coord: TAstNodeCoord; t1, t2: TTypeCode);
  begin
    ParseError(Coord, 'Incompatible types: ''%s'' and ''%s''',
      [TypeNames[t1], TypeNames[t2]]);
  end;

  // Make sure Expr does not point to the Node specified by Kind
  // Return true to indicate that Expr is not in the Node type specified by Kinds
  function NotAllowNode(Kinds: TAstNodeKinds; Expr: TExpr): boolean;
  var
    Invalid: boolean;
    Sym: TSymbol;
  begin
    Invalid := False;
    Sym := Expr.GetReference;
    if Sym <> nil then
    begin
      Invalid := Sym.NodeKind in Kinds;
    end;

    {Invalid := False;
    case Expr.OpCode of
      opSYMBOL:
        if TSymbolExpr(Expr).Reference <> nil then
          Invalid := TSymbolExpr(Expr).Reference.NodeKind in Kinds;
      opMEMBER:
        begin
          Assert(TBinaryExpr(Expr).Right.OpCode = opSYMBOL, 'NotAllowNode');
          Expr := TBinaryExpr(Expr).Right;
          if TSymbolExpr(Expr).Reference <> nil then
            Invalid := TSymbolExpr(Expr).Reference.NodeKind in Kinds;
        end;
    end;}

    if Invalid then
    begin
      if Expr.Typ = nil then
        Expr.Typ := FContext.FAnytype;
      ParseError(Expr.Coord, SErr_InvalidOperand);
    end;
    Result := not Invalid;
  end;

  function EnsureNode(Kind: TAstNodeKind; Expr: TExpr): boolean;
  var
    Kinds: TAstNodeKinds;
  begin
    Kinds := [Low(TAstNodeKind)..High(TAstNodeKind)];
    Exclude(Kinds, Kind);
    Result := NotAllowNode(Kinds, Expr);
  end;

  procedure SubstituteExpr(Old, New: TExpr);
  var
    P: TExpr;
    Kind: integer;
  begin
    P := Old.Parent;
    if P = nil then
      Exit;
    Kind := 0;
    case
      OpKinds[P.OpCode] of
      opkBinary: if TBinaryExpr(P).Left = Old then
          Kind := 1
        else
          Kind := 2;
      opkUnary: Kind := 3;
      opkList: Kind := 4;
    end;
    //    Old.Detach;
    case Kind of
      1: TBinaryExpr(P).Left := New;
      2: TBinaryExpr(P).Right := New;
      3: TUnaryExpr(P).Operand := New;
      4:
      begin
        Kind := TListExpr(P).IndexOf(Old);
        TListExpr(P).Replace(Kind, New);
      end;
    end;
  end;

  // Try constant evaluation, if successful, replace the original expression with the new TConstExpr
  // If it fails, return to the original expression
  function ConstantFold(E: TExpr): TExpr;
  var
    C: TConstExpr;
  begin
    C := Self.CreateConstExpr(opCONST);
    if Self.TryEvalConst(E, C.Value) then
    begin
      if (C.Value.VT >= vtPtr) or (C.Value.VT = vtSet) then
      begin
        C.Typ :=
          E.Typ;
        Include(C.Attr, eaConst);
      end
      else
        CheckConst(C);
      SubstituteExpr(E, C);
      Self.ReleaseExpr(E);
      Result := C;
    end
    else
    begin
      Self.ReleaseExpr(C);
      Result := E;
    end;
  end;

  procedure CheckOpenArrayConstructor(Expr: TUnaryExpr);
  var
    List: TListExpr;
    E: TExpr;
    I: integer;
    Ref: TSymbol;
  begin
    List := TListExpr(Expr.Operand);
    Assert(List <> nil, 'CheckOpenArrayConstructor');
    // Because function overloading may be involved, here is only a basic check.
    // The specific check will be delayed until CheckArrayOfConst CheckArrayOfType
    for I := 0 to List.Count - 1 do
    begin
      E := List.Items[I];
      Ref := E.GetReference;
      if (Ref.NodeKind = nkType) and (TType(Ref).TypeCode <> typClass) then
        ParseError(E.Coord, SErr_InvalidOperand);
      //  NotAllowNode([nkType], E);
      if not (E.Typ.TypeCode in [typInt, typNumeric, typString, typChar, typBool, typPAnsiChar,
        typPWideChar, typVariant, typProcedural, typRecord, typClassRef, typSubrange, typArray, typDynamicArray]) then
      begin
        ParseError(E.Coord, SErr_InvalidOpenArrayEl);
      end;
    end;
    Expr.Typ := FContext.FVarOpenArrayType;
  end;

  function NeedSetType(E: TUnaryExpr): boolean;
  const
    SetOps = [opADD, opSUB, opMUL, opLE, opGE, opEQ, opNE, opIN];
  begin
    if E.Parent = nil then
      Result := True
    else
      Result := E.Parent.OpCode in SetOps;
  end;

  // Check opSET and determine the type. Return true to indicate that it can be regarded as Set
  function CheckSetType(Expr: TUnaryExpr): boolean;
  var
    List: TListExpr;
    E: TExpr;
    I: integer;
    T, T2: TType;
    AllConst: boolean;
  begin
    List := TListExpr(Expr.Operand); // opLIST
    Assert(List <> nil, 'CheckSetType');
    AllConst := True;
    if List.Count > 0 then
    begin
      E := List.Items[0];
      T := E.Typ.NormalType;
      if AllConst then
        AllConst := eaConst in E.Attr;
      case T.TypeCode of
        typBool: Expr.Typ := FContext.FBoolSetType;
        typChar: Expr.Typ := FContext.FCharSetType; // First assume that WideChar is legal
        typEnum: Expr.Typ := GetSetType(TEnumType(T));
        else
          if T.IsInteger then
            Expr.Typ := FContext.FByteSetType
          else
          begin
            Result := False;
            Exit;
          end;
      end;
      Expr.Operand.Typ := Expr.Typ;
      for I := 1 to List.Count - 1 do
      begin
        E := List.Items[I];
        if AllConst then
          AllConst := eaConst in E.Attr;
        T2 := E.Typ;
        // todo 1: Need to check whether the left and right values exceed 0..255
        if T2.TypeCode = typSubrange then
          T2 := TSubrangeType(T2).BaseType;
        if not ((T = T2) or (T.IsInteger and T2.IsInteger)) then
        begin
          Result := False;
          Exit;
        end;
      end;
    end;
    if Expr.Typ = nil then
      Expr.Typ := FContext.FEmptySetType;
    if AllConst then
      Include(Expr.Attr, eaConst);
    Result := True;
  end;

  procedure CheckSetOp(Expr: TUnaryExpr);
  begin
    // There are two situations where set constructor is needed:
    // open array, set
    NotAllowNode([nkType], Expr.Operand);
    // Because function overloading may be involved, here is only a basic check.
    if not CheckSetType(Expr) then
    begin
      if NeedSetType(Expr) then
      begin
        ParseError(Expr.Coord, SErr_InvalidOperand);
        Expr.Typ := FContext.FEmptySetType;
        if Expr.Operand <> nil then
          Expr.Operand.Typ := Expr.Typ;
      end
      else // Check as an open array
        CheckOpenArrayConstructor(Expr);
    end;
  end;

  function NeedExpand(T1, T2: TIntType): boolean; forward;

  procedure CheckRelOp(bin: TBinaryExpr);
  var
    L, R: TType;
    Result: boolean;
  begin
    {integer, real, string, packed string, sets, typed pointer, variant, olevariant}
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    bin.Typ := FContext.FBooleanType;
    L := bin.Left.Typ.NormalType;
    R := bin.Right.Typ.NormalType;
    if (L.TypeCode = typInt) and (R.TypeCode = typInt) then
    begin
      if NeedExpand(TIntType(L), TIntType(R)) then
        DoWarning(bin.Coord, SWarn_CombiningSignedUnsigned);
    end;
    case L.TypeCode of
      typInt,
      typNumeric: if R.TypeCode in [typInt, typNumeric, typVariant] then
        begin
          Result := True;
          if R.TypeCode = typVariant then
            Include(bin.Attr, eaVarOp);
        end
        else
          Result := False;
      typString:
      begin
        Result := R.TypeCode in [typString, typChar, typPAnsiChar, typPWideChar, typVariant];
        if R.TypeCode = typVariant then
          Include(bin.Attr, eaVarOp)
        else
          Include(bin.Attr, eaStrOp);
      end;
      typBool: if R.TypeCode in [typBool, typVariant] then
        begin
          Result := True;
          if R.TypeCode = typVariant then
            Include(bin.Attr, eaVarOp);
        end
        else
          Result := False;
      typVariant:
      begin
        Result := R.TypeCode in [typInt, typNumeric, typChar, typPAnsiChar, typPWideChar,
          typBool, typEnum, typString, typVariant];
        Include(bin.Attr, eaVarOp);
      end;
      typPAnsiChar, typPWideChar: if (L.TypeCode = R.TypeCode) or (R.TypeCode = typPointer) then
          Result := True
        else if R.IsStringCompatible or (R.TypeCode = typChar) then
        begin
          Result := True;
          Include(bin.Attr, eaStrOp);
        end
        else if R.TypeCode = typVariant then
        begin
          Result := True;
          Include(bin.Attr, eaVarOp);
        end
        else
          Result := False;
      {  Result := (L.TypeCode = R.TypeCode) or R.IsStringCompatible
            or (R.TypeCode in [typPointer,
                  typChar,
                //  typPAnsiChar, typPWideChar,
                  typVariant]);}

      // AnsiChar can not compare to WideChar
      typChar:
      begin
        Result := ((R.TypeCode = typChar) and (TCharType(R).Kind = TCharType(L).Kind)) or
          (R.TypeCode in [typString, typPAnsiChar, typPWideChar, typVariant]);
        if Result then
          if R.TypeCode = typVariant then
            Include(bin.Attr, eaVarOp)
          else
            Include(bin.Attr, eaStrOp);
      end;
      typPointer: case R.TypeCode of
          typInterface, typProcedural: Result := bin.Left.OpCode = opNIL;
          else
          // todo 1: If two pointers point to different objects or records, they should not pass
            Result := R.TypeCode in [typPointer, typPAnsiChar, typPWideChar, typClass, typClassRef];
        end;
      typProcedural: if bin.OpCode in [opNE, opEQ] then
        begin
          // an examination
          case
            R.TypeCode of
            typProcedural: Result := TProceduralType(L).IsMethodPointer = TProceduralType(R).IsMethodPointer;
            typPointer: Result := bin.Right.IsNilConst;
            else
              Result := False;
          end;
        end
        else
          Result := False;
      typClass: if bin.OpCode in [opNE, opEQ] then
        begin
          case R.TypeCode
            of
            typPointer: Result := True;
            typClass: Result := TClassType(R).IsInheritedFrom(TClassType(L)) or
                TClassType(L).IsInheritedFrom(TClassType(R));
            else
              Result := False;
          end;
        end
        else
          Result := False;
      typClassRef: if bin.OpCode in [opNE, opEQ] then
        begin
          case R.TypeCode of
            typPointer: Result := True;
            typClassRef: Result := TClassRefType(R).IsInheritedFrom(TClassRefType(L)) or
                TClassRefType(L).IsInheritedFrom(TClassRefType(R));
            else
              Result := False;
          end;
        end
        else
          Result := False;
      typInterface:
      // dispinterface can be the same as IDispatch and the same type of dispinterface
      // interface of the same inheritance tree can be compared
      // They can all be compared with nil
      if bin.OpCode in [opNE, opEQ] then
        begin
          case R.TypeCode of
            typPointer: Result := bin.Right.OpCode = opNIL;
            else
              if TInterfaceType(L).IsDisp then
              begin
                Result := (R = FContext.FIDispatchType) or (L = R);
              end
              else
              begin
                Result := (TInterfaceType(R).IsDisp and (L = FContext.FIDispatchType)) or
                  TInterfaceType(R).IsInheritedFrom(TInterfaceType(L)) or
                  TInterfaceType(L).IsInheritedFrom(TInterfaceType(R));
              end;
          end;
        end
        else
          Result := False;
      typEnum: Result := (L = R) or (R.TypeCode = typVariant);
      typSet:
      begin
        Result := (R.TypeCode = typSet) and (bin.OpCode in [opNE, opEQ, opGE, opLE]) and
          ((TSetType(L).RangeType = nil) or (TSetType(R).RangeType = nil) or
          (TSetType(L).RangeType.Equals(TSetType(R).RangeType)));
        if Result then
        begin
          Include(bin.Attr, eaSetOp);
          if (TSetType(L).RangeType = nil) and (TSetType(R).RangeType = nil) then
            bin.Left.Typ := FContext.FByteSetType
          else if (TSetType(L).RangeType = nil) then
            bin.Left.Typ := R
          else
            bin.Right.Typ := L;
        end;
      end;
      else
        Result :=
          False;
    end;
    if not Result then
      IncompatibleErr(bin.Coord, L.TypeCode, R.TypeCode);
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckIsOp(bin: TBinaryExpr);
  var
    RT: TType;
  begin
    bin.Typ := FContext.FBooleanType;
    if bin.Left.Typ.TypeCode in [typClass, typInterface] then
    begin
      RT := bin.Right.Typ;
      if not (((RT.TypeCode = typClass) and bin.Right.IsTypeSymbol) or (RT.TypeCode = typClassRef)) then
        ParseError(bin.Coord, SErr_InvalidOperand);
    end
    else
      ParseError(bin.Coord, SErr_InvalidOperand);
  end;

  procedure CheckInOp(bin: TBinaryExpr);
  var
    hasErr, notEmpty: boolean;
  begin
    // Left: integer, char, enum
    // right: set
    bin.Typ := FContext.FBooleanType;
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType],
      bin.Right);
    if bin.Right.Typ.TypeCode <> typSet then
      hasErr := True
    else
    begin
      notEmpty := TSetType(bin.Right.Typ).RangeType <> nil;
      case bin.Left.Typ.TypeCode of
        typInt: hasErr := notEmpty and (TSetType(bin.Right.Typ).RangeType <> FContext.FByteRangeType);
        typBool: hasErr := notEmpty and (TSetType(bin.Right.Typ).RangeType <> FContext.FBoolRangeType);
        typChar: hasErr := notEmpty and (TSetType(bin.Right.Typ).RangeType <> FContext.FCharRangeType);
        typEnum: hasErr := notEmpty and (TSetType(bin.Right.Typ).RangeType.BaseType <> TEnumType(bin.Left.Typ));
        else
          hasErr := True;
      end;
    end;
    if hasErr then
      ParseError(bin.Coord, SErr_InvalidOperand);
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
    Include(bin.Attr, eaSetOp);
  end;

  procedure CheckAsOp(bin: TBinaryExpr);
  begin
    NotAllowNode([nkType], bin.Left);
    // On the left is an expression of class, interface type
    // On the right is the class reference expression, interface type symbol
    if bin.Left.Typ.TypeCode in [typClass, typInterface] then
    begin
      case bin.Right.Typ.TypeCode of
        typClassRef: bin.Typ := TClassRefType(bin.Right.Typ).RefType;
        typInterface:
        begin
          bin.Typ := bin.Right.Typ;
          if bin.Right.OpCode <> opSYMBOL then
            ParseError(bin.Coord, SErr_InvalidOperand);
        end;
        else
          bin.Typ := bin.Left.Typ;
          ParseError(bin.Coord, SErr_InvalidOperand);
      end;
    end
    else
    begin
      bin.Left.Typ := FContext.FTObjectType;
      ParseError(bin.Coord, SErr_InvalidOperand);
    end;
  end;

const
  SignOf: array
    [intS8..intU64] of boolean = (True, False, True, False, True, False, True, False);

  function NeedExpand(t1, t2: TIntType): boolean;
  begin
    // LongWord and other signed number operations need to be extended to Int64,
    // which will cause some performance loss
    Result := ((t1.Kind = intU32) and (t2.Kind in [intS8, intS16, intS32])) or
      ((t2.Kind = intU32) and (t1.Kind in [intS8, intS16, intS32]));
  end;

  procedure CheckDivModOp(bin: TBinaryExpr);
  var
    L, R: TType;
  begin
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    L := bin.Left.Typ;
    R := bin.Right.Typ;
    if L.TypeCode = typSubrange then
      L := TSubrangeType(L).BaseType;
    if R.TypeCode = typSubrange then
      R := TSubrangeType(R).BaseType;
    if (L.TypeCode = typInt) and (R.TypeCode = typInt) then
    begin
      if (TIntType(L).Kind in [intU32..intU64]) or (TIntType(R).Kind in [intU32..intU64]) then
      begin
        if NeedExpand(TIntType(L), TIntType(R)) then
          DoWarning(bin.Coord, SWarn_CombiningSignedUnsigned);
        if SignOf[TIntType(L).Kind] or SignOf[TIntType(R).Kind] then
          bin.Typ := FContext.FInt64Type
        else
          bin.Typ := FContext.FUInt64Type;
      end
      else
        bin.Typ := FContext.FLongIntType;
    end
    else if (L.TypeCode = typVariant) then
    begin
      if not TypIsVariantArithCompatible(R) then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FVariantType;
      Include(bin.Attr, eaVarOp);
    end
    else if (R.TypeCode = typVariant) then
    begin
      if not TypIsVariantArithCompatible(L) then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FVariantType;
      Include(bin.Attr, eaVarOp);
    end
    else
    begin
      bin.Typ := FContext.FLongIntType;
      ParseError(bin.Coord, SErr_InvalidOperand);
    end;
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckDivOp(bin: TBinaryExpr);
  var
    L, R: TType;
  begin
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    L := bin.Left.Typ;
    R := bin.Right.Typ;
    if L.TypeCode = typSubrange then
      L := TSubrangeType(L).BaseType;
    if R.TypeCode = typSubrange then
      R := TSubrangeType(R).BaseType;
    if (L.TypeCode in [typInt, typNumeric]) and (R.TypeCode in [typInt, typNumeric]) then
    begin
      bin.Typ := FContext.FDoubleType;
    end
    else if (L.TypeCode = typVariant) or (R.TypeCode = typVariant) then
    begin
      if not TypIsVariantArithCompatible(L) or not TypIsVariantArithCompatible(R) then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FVariantType;
      Include(bin.Attr, eaVarOp);
    end
    else
    begin
      bin.Typ := FContext.FLongIntType;
      ParseError(bin.Coord, SErr_InvalidOperand);
    end;
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckNegOp(un: TUnaryExpr);
  var
    T: TType;
  begin
    NotAllowNode([nkType], un.Operand);
    T := un.Operand.Typ.NormalType;
    case T.TypeCode of
      typInt: un.Typ := T;
      typNumeric: case TNumericType(T).Kind of
          numCurrency: un.Typ := FContext.FCurrencyType;
          numSingle: un.Typ := FContext.FSingleType;
          else un.Typ := FContext.FDoubleType;
        end;
      typVariant:
      begin
        un.Typ := T; // FContext.FVariantType;
        Include(un.Attr, eaVarOp);
      end;
      else
        un.Typ := FContext.FLongIntType;
        ParseError(SErr_InvalidOperand);
    end;
    if eaConst in un.Operand.Attr then
      Include(un.Attr, eaConst);
  end;

  // opADD opSUB opMUL
  procedure CheckAddSubMulOp(bin: TBinaryExpr);
  var
    t1, t2: TTypeCode;
    L, R: TType;
  begin
    {
      integer, real, string, packed string, sets, typed pointer, variant, olevariant
    }
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    L := bin.Left.Typ.NormalType;
    R := bin.Right.Typ.NormalType;
    // todo 1: The constant must be changed to avoid expansion to 64-bit operations
    t1 := L.TypeCode;
    t2 := R.TypeCode;
    if (t1 in [typInt, typNumeric]) and (t2 in [typInt, typNumeric]) then
    begin
      if (t1 = typInt) and (t2 = typInt) then
      begin
        if (TIntType(L).Kind <= intS32) and (TIntType(R).Kind <= intS32) then
        begin   // byte and word can be transformed into longint, so the result of the operation is regarded as longint
          bin.Typ := FContext.FLongintType;
        end
        else if (TIntType(L).Kind = intU64) or (TIntType(R).Kind = intU64) then
        begin   // The result of the operation with Uint64 is UInt64
          bin.Typ := FContext.FUInt64Type;
        end
        else if (TIntType(L).Kind in [intS8, intS16, intS32, intS64]) or (TIntType(R).Kind in
          [intS8, intS16, intS32, intS64]) then
        begin   // shortint, smallint, longint, int64 and LongWord operations, the result is int64
          bin.Typ := FContext.FInt64Type;
        end
        else   // byte, word, longword and longword operations, the result is longword, no need to be converted to int64
          bin.Typ := FContext.FLongWordType;
        // Check whether the operation needs to be extended to 64 bits
        if NeedExpand(TIntType(L), TIntType(R)) then
          DoWarning(bin.Coord, SWarn_CombiningSignedUnsigned);
      end
      else
      begin
        // Operate with Currency, the result is Currency, otherwise it is Double
        if ((t1 = typNumeric) and (TNumericType(L).Kind = numCurrency)) or
          ((t2 = typNumeric) and (TNumericType(R).Kind = numCurrency)) then
          bin.Typ := FContext.FCurrencyType
        else
          bin.Typ := FContext.FDoubleType;
      end;
    end
    else if (t1 = typVariant) or (t2 = typVariant) then
    begin
      if not TypIsVariantArithCompatible(L) or not TypIsVariantArithCompatible(R) then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FVariantType;
      Include(
        bin.Attr, eaVarOp);
    end
    // string
    else if (bin.OpCode = opADD) and L.IsStringArithCompatible and R.IsStringArithCompatible then
    begin
      if L.IsUnicodeString or R.IsUnicodeString then
        bin.Typ := FContext.FUnicodeStringType
      else if L.IsWideString or R.IsWideString then
        bin.Typ := FContext.FWideStringType
      // todo 8: do it later
       {ShortString addition, you need to check the total length, if it exceeds 255, it will be converted to string addition, this function
        Save it to be implemented later, now regardless of the length, it is converted to string
       else if (t1 = typShortString) or (t2 = typShortString) then
         bin.Typ := FContext.FTypes[typShortString]}
      else
        bin.Typ := FContext.FStringType;
      Include(bin.Attr, eaStrOp);
    end
    else if (bin.OpCode = opSUB) and (t1 in [typPointer, typPAnsiChar, typPWideChar]) and
      (t2 in [typPointer, typPAnsiChar, typPWideChar]) then
    begin
      bin.Typ := FContext.FNativeIntType;
    end
    // pointer arithmetic
     // p := 1 + p: ok
     // p := 1-p: error
    else if (bin.OpCode in [opADD, opSUB]) and (t1 in [typPointer, typPAnsiChar, typPWideChar]) and (t2 = typInt) then
    begin
      if (t1 = typPointer) and TPointerType(L).IsUntype then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := L;
    end
    else if (bin.OpCode in [opADD]) and (t2 in [typPointer, typPAnsiChar, typPWideChar]) and (t1 = typInt) then
    begin
      if (t2 = typPointer) and TPointerType(R).IsUntype then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.
        Typ := R;
    end
    // Set operations
    else if (t1 = typSet) and (t2 = typSet) then
    begin
      if (TSetType(L).RangeType <> nil) and (TSetType(R).RangeType <> nil) and not
        TSetType(L).RangeType.Equals(TSetType(R).RangeType) then
        //        IncompatibleErr(bin.Coord, t1, t2);
        ParseError(bin.Coord, 'Incompatible types');
      //bin.Typ := GetSetOpType(L, R);
      bin.Typ := L;
      Include(bin.Attr, eaSetOp);
    end
    else
    begin
      bin.Typ := FContext.FLongIntType;
      ParseError(bin.Coord,
        SErr_InvalidOperand);
    end;
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckShiftOp(bin: TBinaryExpr);
  var
    L, R: TType;
  begin
    {
       shl: If the left operand is less than Integer, the result is of type Integer. Otherwise, the result is the type of left operand
       shr result type is inferred to be the type of left operand
    }
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    L := bin.Left.Typ.NormalType;
    R := bin.Right.Typ.NormalType;
    if (L.TypeCode = typInt) and (R.TypeCode = typInt) then
    begin
      if (TIntType(L).Kind < intS32) and (bin.OpCode = opSHL) then
        bin.Typ := FContext.FLongintType
      else
        bin.Typ := L;
    end
    else if (L.TypeCode = typVariant) or (R.TypeCode = typVariant) then
    begin
      if not TypIsVariantArithCompatible(L) or not TypIsVariantArithCompatible(R) then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FVariantType;
      Include(bin.Attr, eaVarOp);
    end
    else
    begin
      bin.Typ := FContext.FLongintType;
      ParseError(bin.Coord, SErr_InvalidOperand);
    end;
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckBitwiseOp(bin: TBinaryExpr);
  var
    t1, t2: TTypeCode;
    L, R: TType;
  begin
    {
      variant, olevariant, integer, boolean
    }
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    L := bin.Left.Typ.NormalType;
    R := bin.Right.Typ.NormalType;
    {
       Sign speculation of and or xor result:
         unsigned op unsigned: unsigned
         unsigned op signed: \
                              |=> unsigned
         signed op unsigned: /
         signed op signed: signed
         0..$7fffffff constant can change the type. Otherwise, no.
    }
    t1 := L.TypeCode;
    t2 := R.TypeCode;
    if (t1 = typInt) and (t2 = typInt) then
    begin
      if L.Size = R.Size then
      begin
        if R.IsSignedInt then
          bin.Typ := L
        else
          bin.Typ := R;
      end
      else if L.Size < R.Size then
        bin.Typ := R
      else
        bin.Typ := L;
    end
    else if (t1 = typVariant) or (t2 = typVariant) then
    begin
      if not TypIsVariantArithCompatible(L) or not TypIsVariantArithCompatible(R) then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FVariantType;
      Include(bin.Attr, eaVarOp);
    end
    else if (bin.OpCode in [opAND, opOR, opXOR]) and (t1 = typBool) and (t2 = typBool) then
    begin
      bin.Typ := FContext.FBooleanType;
    end
    else
    begin
      bin.Typ := FContext.FLongintType;
      ParseError(bin.Coord, SErr_InvalidOperand);
    end;
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckNotOp(un: TUnaryExpr);
  var
    T: TType;
  begin
    NotAllowNode([nkType], un.Operand);
    T := un.Operand.Typ.NormalType;
    case T.TypeCode of
      typInt: un.Typ := T;
      typBool: un.Typ := T;
      typVariant:
      begin
        un.Typ := T;
        Include(un.Attr, eaVarOp);
      end;
      else
        un.Typ := FContext.FBooleanType;
        ParseError(SErr_InvalidOperand);
    end;
    if eaConst in un.Operand.Attr then
      Include(un.Attr, eaConst);
  end;

  function CreateCallExpr(E: TExpr): TBinaryExpr;
  begin
    { Left := Sym.Parent;
      if (Left = nil) or (Left.OpCode <> opMEMBER) then Left := Sym;
    }
    Result := CreateBinaryExpr(opCALL, nil, CreateListExpr);
    Result.Attr := E.Attr;
    Result.Coord := E.Coord;
    Result.Switches := E.Switches;
    // Result.Next := Left.Next;
    // Left.Next := nil;
    SubstituteExpr(E, Result);
    Result.Left := E;
  end;

  function CreateProcAddrExpr(E: TExpr): TUnaryExpr;
  var
    AddrExpr: TUnaryExpr;
  begin
    //    Assert(E.Typ.TypeCode = typProcedural, 'CreateProcAddrExpr: Require E is procedural type');
    AddrExpr := Self.CreateUnaryExpr(opADDR, nil);
    AddrExpr.Typ := E.Typ;
    AddrExpr.Coord := E.Coord;
    SubstituteExpr(E, AddrExpr);
    AddrExpr.Operand := E;
    Result := AddrExpr;
  end;

  function GetProcType(Sym: TSymbol): TProceduralType;

    function GetProc(T: TType):
    TProceduralType;
    begin
      if T.TypeCode = typProcedural then
        Result := TProceduralType(T)
      else
        Result := nil;
    end;

  begin
    case Sym.NodeKind of
      nkFunc, nkMethod, nkExternalFunc: Result := TFunctionDecl(Sym).ProceduralType;
      nkVariable: Result := GetProc(TVariable(Sym).VarType);
      nkField: Result := GetProc(TField(Sym).FieldType);
      nkProperty: Result := GetProc(TProperty(Sym).PropType);
      nkIntfProperty: Result := GetProc(TIntfProperty(Sym).PropType);
      nkFuncParam: Result := GetProc(TFuncParam(Sym).ParamType);
      else
        Result := nil;
    end;
  end;

  function GetReturnType(Sym: TSymbol): TType;

    function GetRet(T: TType): TType;
    begin
      if T.TypeCode = typProcedural then
        Result := TProceduralType(T).ReturnType
      else
        Result := nil;
    end;

  begin
    case Sym.NodeKind
      of
      nkFunc, nkMethod, nkExternalFunc: Result := TFunctionDecl(Sym).ReturnType;
      nkVariable: Result := GetRet(TVariable(Sym).VarType);
      nkField: Result := GetRet(TField(Sym).FieldType);
      nkProperty: Result := GetRet(TProperty(Sym).PropType);
      nkIntfProperty: Result := GetRet(TIntfProperty(Sym).PropType);
      nkFuncParam: Result := GetRet(TFuncParam(Sym).ParamType);
      else
        Result := nil;
    end;
  end;

  function MinOfProcParams(Sym: TSymbol): integer;
  begin
    case
      Sym.NodeKind of
      nkFunc, nkMethod, nkExternalFunc: Result := TFunctionDecl(Sym).MinOfParams
      else
        Sym := GetProcType(Sym);
        Result := TProceduralType(Sym).MinOfParams;
    end;
  end;

  function IsCtor(Sym: TSymbol): boolean;
  begin
    Result := (Sym.NodeKind = nkMethod) and (TMethod(Sym).MethodKind = mkConstructor);
  end;

type
  TCheckArgsResult = (caMismatched, caOk, caCompatible);
  TCheckOverloadResult = (coNonMatched, coMatched, coMultiMatched, coCompatible, coMultiCompatible);

  // Only when IsOverload=True is it possible to return caOk
  function CheckArgs(FormalArgs: TFuncParamList; CallExpr: TBinaryExpr; ErrReport: boolean = True;
    IsOverload: boolean = False; // Located in Overload
    DoChange: boolean = True; // If the actual parameter is the symbol of Overload, you can adjust the TFunctionDecl it points to
    IsVarArgs: boolean = False // Is there a varargs declaration
    ): TCheckArgsResult; overload;

    procedure ShowError(const Coord: TAstNodeCoord; const Msg: string);
    begin
      if ErrReport then
        ParseError(Coord, Msg);
    end;

    procedure ChangeType(ActualArg: TExpr; ArgTyp: TType);
    begin
      // change type
      if DoChange and (ActualArg.Typ.TypeCode = typSet) then
      begin
        ActualArg.
          Typ := ArgTyp;
        if TUnaryExpr(ActualArg).Operand <> nil then
          TUnaryExpr(ActualArg).Operand.Typ := ActualArg.Typ;
      end;
    end;

    // Check if typ is open array compatible
    function IsOpenArrayCompatibility(typ, el: TType): boolean;
    begin
      case typ.TypeCode of
        typOpenArray: Result := (el = FContext.FVarRecType);
        typDynamicArray: Result := TDynamicArrayType(typ).ElementType.Equals(el);
        typArray: Result := TArrayType(typ).ElementType.Equals(el);
        typSet: Result := True;
        else
          Result := False;
      end;
    end;

    // check variant open array
    procedure CheckArrayOfConst(ActualArg: TExpr);
    begin
      if not IsOpenArrayCompatibility(ActualArg.Typ, FContext.FVarRecType) then
        ShowError(ActualArg.Coord, SErr_VarArgMustIdentical);
      ChangeType(ActualArg, FContext.FVarOpenArrayType);
    end;

    procedure CheckArrayOfType(ActualArg: TExpr; ArgDef: TFuncParam);
    var
      List: TListExpr;
      E: TExpr;
      I: integer;
    begin
      if ActualArg.OpCode = opSET then
      begin
        List := TListExpr(TUnaryExpr(ActualArg).Operand);
        for I := 0 to List.Count - 1 do
        begin
          E := List.Items[I];
          if not CheckAssignCompatibility(E.Typ, TOpenArrayType(ArgDef.ParamType).ElementType) then
            ShowError(E.Coord, SErr_IncompatibleTypes);
        end;
        // change type
        ChangeType(ActualArg, ArgDef.ParamType);
      end
      else
      begin
        if not IsOpenArrayCompatibility(ActualArg.Typ, ArgDef.ParamType) then
          ShowError(ActualArg.Coord, SErr_IncompatibleTypes);
        ChangeType(ActualArg, ArgDef.ParamType);
      end;
    end;

    function MinCountOfArgs(Args: TFuncParamList): integer;
    var
      i: integer;
    begin
      Result := 0;
      for i := 0 to Args.Count - 1 do
        if Args[i].DefaultValue.VT = vtEmpty then
          Inc(Result);
    end;

    // Check the type compatibility of actual and formal parameters
    // T1 formal parameter type, T2 actual parameter type, E, actual parameter expression
    function CheckTypeCompatibility(T1, T2: TType; E: TExpr): boolean;
    var
      Temp: TType;
    begin
      if (T1 <> nil) and (T2 <> nil) then
      begin
        if (T1.TypeCode = typClass) and (T2.TypeCode = typClass) and E.IsCtorSymbol then
        begin
          Result := TClassType(T1).IsInheritedFrom(TClassType(T2));
          Exit;
        end;
        Temp := E.Typ;
        E.Typ := T2;
        Result := Self.CanAssign(T1, E);
        if not (Result and (E.Typ <> Temp)) then
          E.Typ := Temp;
        //Result := CheckAssignCompatibility(T1, T2)
      end
      else
        Result := False;
    end;

    function CheckProcCompatibility(T1, T2: TType): boolean;
    begin
      if (T1 <> nil) and (T2 <> nil) then
      begin
        // This allows function pointers to be passed to untyped pointers
        if ((T2.TypeCode = typProcedural) and not TProceduralType(T2).IsMethodPointer) and T1.IsUntypePointer then
          Result :=
            True
        else
          Result := CheckAssignCompatibility(T1, T2);
      end
      else
        Result := False;
    end;

    // Check if the actual parameters are compatible
    function CheckExprCompatibility(Param: TFuncParam; E: TExpr): TCheckArgsResult;
    var
      Typ: TProceduralType;
      AlterTyp: TType;
      Ok: boolean;
    begin
      if E.Typ.TypeCode = typProcedural then
        Typ := TProceduralType(E.Typ)
      else
        Typ := nil;
      if Typ <> nil then
      begin
        AlterTyp := Typ;
        Ok := CheckTypeCompatibility(Param.ParamType, AlterTyp, E);
        if not Ok and (Typ.MinOfParams = 0) then
        begin
          AlterTyp :=
            Typ.ReturnType;
          if AlterTyp <> nil then
          begin
            Ok := CheckTypeCompatibility(Param.ParamType, AlterTyp, E);
            if Ok and DoChange then
              Include(E.Attr, eaCall);
          end;
        end;
        if not Ok then
          Result := caMismatched
        else if IsOverload and Param.ParamType.Equals(AlterTyp) then
          Result := caOk
        else
          Result := caCompatible;
      end
      else
        Result := caMismatched;
    end;

    // Check if the types of the actual parameters are compatible. Ref is the symbol pointed to by E
    function CheckSingleCompatibility(Param: TFuncParam; E: TExpr; Ref: TSymbol): TCheckArgsResult;
    var
      AlterTyp: TType;
      Ok: boolean;
    begin
      if E.OpCode = opADDR then
      begin
        AlterTyp := GetProcType(Ref);
        if AlterTyp <> nil then
          Ok := CheckProcCompatibility(Param.ParamType, AlterTyp)
        else
          Ok := False;
        if Ok and DoChange then
          TUnaryExpr(E).Operand.SetReference(Ref);
      end
      else
      begin
        if not IsCtor(Ref) then
        begin
          AlterTyp := GetProcType(Ref);
          Ok := CheckTypeCompatibility(Param.ParamType, AlterTyp, E);
        end
        else
          Ok := False;
        if not Ok and (MinOfProcParams(Ref) = 0) then
        begin
          //AlterTyp := Ref.ReturnType;
          AlterTyp := GetReturnType(Ref);
          if AlterTyp <> nil then
          begin
            Ok := CheckTypeCompatibility(Param.ParamType, AlterTyp, E);
            if Ok and DoChange then
            begin
              Include(E.Attr, eaCall);
              E.SetReference(Ref);
            end;
          end;
        end;
      end;
      if not Ok then
        Result := caMismatched
      else if IsOverload and Param.ParamType.Equals(AlterTyp) then
        Result := caOk
      else
        Result := caCompatible;
    end;

    function CheckGroupCompatibility(Arg: TFuncParam; E: TExpr; Func: TFunctionDecl):
    TCheckOverloadResult;
    var
      ChkResult: TCheckArgsResult;
      F: TFunctionDecl;
    begin
      Result :=
        coNonMatched;
      F := Func;
      while F <> nil do
      begin
        ChkResult := CheckSingleCompatibility(Arg, E, F);
        if ChkResult = caOk then
        begin
          Result := coMatched;
          Break;
        end
        else if ChkResult = caCompatible then
        begin
          Result := coCompatible;
          Break;
        end;
        F := F.NextOverload;
      end;
    end;

    function CheckMultiCompatibility(Arg: TFuncParam; E: TExpr; Func: TFunctionDecl): TCheckArgsResult;
    var
      ChkResult: TCheckOverloadResult;
    begin
      Result := caMismatched;
      if not (eaOverloadRestrict in E.Attr) and (fmOverload in Func.Modifiers) then
      begin
        GetOverloadBegin(Func);
        while
          Func <> nil do
        begin
          ChkResult := CheckGroupCompatibility(Arg, E, Func);
          case ChkResult
            of
            coCompatible: Result := caCompatible;
            coMatched:
            begin
              Result := caOk;
              Exit;
            end;
          end;
          Func := GetOverloadNext;
        end;
        GetOverloadEnd;
      end
      else if Func.NextOverload <> nil then
      begin
        ChkResult := CheckGroupCompatibility(Arg, E, Func);
        case ChkResult of
          coCompatible: Result := caCompatible;
          coMatched:
          begin
            Result := caOk;
            Exit;
          end;
        end;
      end;
    end;

    function CheckCompatible(T: TType; E: TExpr): boolean;
    begin
      Result := CanAssign(T, E);
    end;

    function CheckCompatibility(Arg: TFuncParam; E: TExpr): TCheckArgsResult;
    var
      Ref: TSymbol;
    begin
      if eaDelayed in E.Attr then
      begin
        Ref := nil;
        case E.OpCode of
          opSYMBOL, opMEMBER: Ref := E.GetReference;
          opADDR: if TUnaryExpr(E).Operand <> nil then
              Ref := TUnaryExpr(E).Operand.GetReference;
          else
            // Other expressions that return function pointers (added in CheckAdjustCall) such as aaa(TMyFunc(p));
            //Result := caMismatched;
            Result := CheckExprCompatibility(Arg, E);
            Exit;
        end;
        // Ref is not necessarily a function, it may be a variable of a function pointer
        if Ref <> nil then
        begin
          if (Ref.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) and TFunctionDecl(Ref).IsOverload then
          begin
            Result := CheckMultiCompatibility(Arg, E, TFunctionDecl(Ref));
          end
          else
            Result := CheckSingleCompatibility(Arg, E, Ref);
        end
        else
          Result := caMismatched;
      end
      else
      begin
        if not CheckCompatible(Arg.ParamType, E) then
        begin
          Result := caMismatched;
        end
        else if IsOverload and Arg.ParamType.Equals(E.Typ) then
          Result := caOk
        else
          Result := caCompatible;
      end;
    end;

  var
    ArgCount, FormalArgCount, MinArgCount, I: integer;
    E: TExpr;
    Arg: TFuncParam;
    ActualArgs: TListExpr;
    AllOk: boolean;
  begin
    FormalArgCount := 0;
    MinArgCount := 0;
    if FormalArgs <> nil then
    begin
      FormalArgCount := FormalArgs.Count;
      MinArgCount := MinCountOfArgs(FormalArgs);
    end;
    ActualArgs := TListExpr(CallExpr.Right);
    ArgCount := ActualArgs.Count;
    Result := caMismatched;
    AllOk := True;
    if IsVarargs and (ArgCount > FormalArgCount) then
      ArgCount := FormalArgCount;
    if (ArgCount <= FormalArgCount) and (ArgCount >= MinArgCount) then
    begin
      if ArgCount > 0 then
      begin
        I := 0;
        while I < ArgCount do
        begin
          E := ActualArgs.Items[I];
          Arg := FormalArgs[I];
          if Arg.ArgKind in [akArrayOfType, akArrayOfConst] then
          begin
            // Check open array parameters
            if TOpenArrayType(Arg.ParamType).ElementType.TypeCode = typUntype then
              CheckArrayOfConst(E)
            else
              CheckArrayOfType(E, Arg);
            if Arg.Modifier in [argVar, argOut] then
              if not E.HasMemory then
                ShowError(E.Coord, SErr_VarArgMustIdentical);
          end
          else if Arg.ArgKind = akUntype then
          begin
            if not E.HasMemory then
              ShowError(E.Coord, SErr_IncompatibleTypes);
          end
          else if Arg.Modifier in [argVar, argOut] then
          begin
            if not E.HasMemory then
              ShowError(E.Coord, SErr_IncompatibleTypes)
            else if (Arg.ParamType.TypeCode <> typUntype) and not E.Typ.Equals(Arg.ParamType) then
            // var/out parameters must be strictly equal
            begin
              ShowError(E.Coord, SErr_VarArgMustIdentical);
              Exit;
            end;
          end
          else
          begin
            case CheckCompatibility(Arg, E)
              of
              caMismatched:
              begin
                ShowError(E.Coord, SErr_IncompatibleTypes);
                Exit;
              end;
              caCompatible: AllOk := False;
            end;
          end;
          Inc(I);
        end;
      end;
    end
    else
    begin
      ShowError(CallExpr.Coord, SErr_ArgNotMatched);
      Exit;
    end;
    if AllOk and IsOverload then
      Result := caOk
    else
      Result := caCompatible;
  end;

  // Check a set of overloaded functions
  function CheckFuncs(var Func: TFunctionDecl; CallExpr: TBinaryExpr): TCheckOverloadResult;
  var
    ChkResult: TCheckArgsResult;
    MatchedCount, CompatibleCount: integer;
    F: TFunctionDecl;
  begin
    MatchedCount := 0;
    CompatibleCount := 0;
    Result := coNonMatched;
    F := Func;
    while F <> nil do
    begin
      ChkResult := CheckArgs(F.Params, CallExpr, False, True, False, fmVarargs in Func.Modifiers);
      if ChkResult = caOk then
      begin
        Inc(MatchedCount);
        if MatchedCount = 1 then
          Func := F;
      end;
      if ChkResult = caCompatible then
      begin
        Inc(CompatibleCount);
        if (CompatibleCount = 1) and (MatchedCount = 0) then
          Func := F;
      end;
      F := F.NextOverload;
    end;
    if MatchedCount > 0 then
    begin
      if MatchedCount = 1 then
        Result := coMatched
      else
        Result := coMultiMatched;
    end
    else if CompatibleCount > 0 then
    begin
      if CompatibleCount = 1 then
        Result := coCompatible
      else
        Result := coMultiCompatible;
    end;
  end;

  procedure ProcessDelayed(CallExpr: TBinaryExpr);
  var
    Args: TListExpr;
    E: TExpr;
    I: integer;
    NewExpr: TBinaryExpr;
    Ref: TSymbol;
  begin
    if CallExpr = nil then
      Exit;
    Args := TListExpr(CallExpr.Right);
    if Args = nil then
      Exit;
    for I := 0 to
      Args.Count - 1 do
    begin
      E := Args.Items[I];
      if eaCall in E.Attr then
      begin
        Exclude(E.Attr, eaDelayed);
        Exclude(E.Attr, eaCall);
        NewExpr := CreateCallExpr(E);
        Ref := E.GetReference;
        if Ref <> nil then
          NewExpr.Typ := GetReturnType(Ref);
        if NewExpr.Typ = nil then
          NewExpr.Typ := FContext.FUntype;
      end
      else if eaDelayed in E.Attr then
      begin
        Exclude(E.Attr, eaDelayed);
        if E.GetFunctionSymbol <> nil then
        begin
          // So far it should be a function pointer, add a @
          Assert(E.OpCode <> opADDR);
          CreateProcAddrExpr(E);
        end;
      end;
    end;
  end;

  procedure CheckArgs(var Func: TFunctionDecl; CallExpr: TBinaryExpr); overload;
  var
    ChkResult: TCheckOverloadResult;
    FirstOk, Old: TFunctionDecl;
  begin
    if fmOverload in Func.Modifiers then
    begin
      // There is an overflow command, you can search across a range
      GetOverloadBegin(Func);
      Old := Func;
      FirstOk :=
        nil;
      while Func <> nil do
      begin
        ChkResult := CheckFuncs(Func, CallExpr);
        case ChkResult of
          coCompatible: if FirstOk = nil then
            FirstOk := Func;
          coMatched:
          begin
            FirstOk := Func;
            Break;
          end;
          coMultiMatched:
          begin
            ParseError(CallExpr.Coord, 'Ambiguous overloaded call to %s', [Old.Name]);
            Exit;
          end;
        end;
        Func := GetOverloadNext;
      end;
      GetOverloadEnd;
      if FirstOk <> nil then
      begin
        Func := FirstOk;
        CheckArgs(Func.Params, CallExpr, True, True, True);
        ProcessDelayed(CallExpr);
        Exit;
      end;
      Func := Old;
      ParseError(CallExpr.Coord, 'There is no overloaded version of %s that can be called with these arguments',
        [Old.Name]);
    end
    else if Func.NextOverload <> nil then
    begin
      Old := Func;
      ChkResult := CheckFuncs(Func, CallExpr);
      case ChkResult of
        coCompatible, coMatched:
        begin
          CheckArgs(Func.Params, CallExpr, True, True, True);
          ProcessDelayed(CallExpr);
          Exit;
        end;
        coMultiCompatible, coMultiMatched:
        begin
          ParseError(CallExpr.Coord, 'Ambiguous overloaded call to %s', [Old.Name]);
          Exit;
        end;
      end;
      Func := Old;
      ParseError(CallExpr.Coord, 'There is no overloaded version of %s that can be called with these arguments',
        [Old.Name]);
    end
    else
    begin
      CheckArgs(Func.Params, CallExpr, True, False, True, fmVarargs in Func.Modifiers);
      ProcessDelayed(CallExpr);
    end;
  end;

  {// Find a function with no parameters and return value
  procedure FindOverloadNoArgs(var Func: TFunctionDecl);
  begin
    if fmOverload in Func.Modifiers then
    begin
      Parser.GetOverloadBegin(Func);
    end
    else if Func.NextOverload <> nil then
    begin
      Old := Func;
      ChkResult := CheckFuncs(Func, CallExpr);
      case ChkResult of
        coCompatible, coMatched: Exit;
        coMultiCompatible, coMultiMatched:
          Parser.ParseError(Old.Coord, 'Ambiguous overloaded call to %s', [Old.Name]);
      end;
      Func := Old;
      Parser.ParseError(CallExpr.Coord,
        'There is no overloaded version of %s that can be called with these arguments',
        [Old.Name]);
    end;
  end;    }
  function CheckBuiltinArgs(Kind: TBuiltinFunctionKind; CallExpr: TBinaryExpr; var Typ: TType): TExpr;
  var
    Num: integer;
    A1, A2, A3: TExpr;
    ActualArgs: TListExpr;

    procedure CheckAbs;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.TypeCode in [typInt, typNumeric]) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched2, ['abs']);
      Typ := A1.Typ;
    end;

    procedure CheckCopy;
    begin
      if Num = 3 then
      begin
        // copy string or array
        NotAllowNode([nkType], A1);
        NotAllowNode([nkType], A2);
        NotAllowNode([nkType], A3);
        if not A1.Typ.IsStringCompatible and (A1.Typ.TypeCode <> typDynamicArray) then
          ParseError(A1.Coord, SErr_IncompatibleTypes)
        else if not A2.Typ.IsInteger then
          ParseError(A2.Coord, SErr_IncompatibleTypes)
        else if not A3.Typ.IsInteger then
          ParseError(A3.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched2, ['copy']);
      Typ := A1.Typ;
    end;

    procedure CheckAddr;
    begin
      // The address taken by Addr is untyped, regardless of the state of $T
      if Num = 1 then
      begin
        if not (A1.HasMemory or A1.IsFunction) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched2, ['addr']);
      Typ := FContext.FPointerType;
    end;

    procedure CheckAssigned;
    begin
      // Assigned parameter requirements are pointers
      if Num = 1 then
      begin
        NotAllowNode([nkType, nkFunc, nkMethod, nkExternalFunc], A1);
        if not A1.Typ.IsPointer and not A1.Typ.IsProcedural then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched2, ['assigned']);
      Typ := FContext.FBooleanType;
    end;

    // Break/Continue
    procedure CheckBrCont;
    begin
      if [psInWhileStmt, psInRepeatStmt, psInForEachStmt, psInForStmt] * FCurStates = [] then
        ParseError(CallExpr.Coord, SErr_OutsideOfLoop);
      if Num <> 0 then
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckChr;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not A1.Typ.IsInteger then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FCharType;
    end;

    procedure CheckDispose;
    begin
      // todo 1: Need to add this form of Dispose(obj, Init)
      // must be a pointer
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not A1.Typ.IsPointer then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckExclude;
    var
      T: TType;
    begin
      if Num = 2 then
      begin
        if not (A1.HasMemory and (A1.Typ.TypeCode = typSet)) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
        T := A2.Typ;
        if T.TypeCode = typSubrange then
          T := TSubrangeType(T).BaseType;
        //        if not ((A2.Typ.TypeCode = typSubrange) and
        //                (TSubrangeType(A2).BaseType = TSetType(A1.Typ).RangeType.BaseType)) then
        if T <> TSetType(A1.Typ).RangeType.BaseType then
          ParseError(A2.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckExit;
    var
      V: TVariable;
    begin
      if not (psInFunc in FCurStates) then
        ParseError(CallExpr.Coord, SErr_IncompatibleTypes);
      if Num = 1 then
      begin
        V := A1.GetVariableSymbol;
        if (FCurFunction.ReturnType = nil) or not CheckAssignCompatibility(FCurFunction.ReturnType, A1.Typ) or
          ((V <> nil) and (vaResult in V.VarAttr)) then
          ParseError(A2.Coord, SErr_IncompatibleTypes);
      end
      else if Num <> 0 then
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckFinalize;
    begin
      if Num = 2 then
      begin
        if not (A1.HasMemory) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
        if not (A2.Typ.IsInteger) then
          ParseError(A2.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckFreeMem;
    begin
      if Num in [1, 2] then
      begin
        NotAllowNode([nkType], A1);
        {if not A1.HasMemory then
          Parser.ParseError(A1.Coord, SErr_VarRequired);}
        if not A1.Typ.IsPointer then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
        if (Num = 2) and not A2.Typ.IsInteger then
          ParseError(A2.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckGetMem;
    begin
      if Num = 2 then
      begin
        NotAllowNode([nkType], A2);
        if not A1.HasMemory then
          ParseError(A1.Coord, SErr_VarRequired);
        if not A1.Typ.IsPointer then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
        if not A2.Typ.IsInteger then
          ParseError(A2.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckInc;
    begin
      if Num in [1, 2] then
      begin
        if Num > 1 then
          NotAllowNode([nkType], A2);
        if not A1.HasMemory then
          ParseError(A1.Coord, SErr_VarRequired);
        if A1.Typ.IsUntypePointer or not (A1.Typ.IsOrdinal or A1.Typ.IsPointer) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
        if Num > 1 then
          if not (A2.Typ.IsInteger) then
            ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckHi;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.TypeCode = typInt) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FByteType;
    end;

    procedure CheckHigh;
    begin
      // high parameter can be type name such as Shortin
      if Num = 1 then
      begin
        if not ((A1.Typ.TypeCode in [typArray, typDynamicArray, typString]) or A1.Typ.IsOrdinal) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      if (A1 <> nil) and (A1.Typ.IsOrdinal) then
        Typ := A1.Typ
      else
        Typ := FContext.FIntegerType;
    end;

    procedure CheckLength;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.TypeCode in [typArray, typDynamicArray, typString]) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FIntegerType;
    end;

    procedure CheckNew;
    begin
      // todo 1: Need to add the form New(obj, Init)
      // New requires pointer type parameters
      if Num = 1 then
      begin
        if not A1.HasMemory then
          ParseError(A1.Coord, SErr_VarRequired);
        if not A1.Typ.IsPointer then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
//        NotAllowNode([nkType]);
//        if not (A1.HasMemory and (Typ.TypeCode = typPointer)) then
//          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckOdd;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.IsInteger) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FBooleanType;
    end;

    function GetUnderlineType(T: TType): TType;
    begin
      case A1.Typ.TypeCode of
        typEnum: Result := FContext.TypeOfRange(TEnumType(A1.Typ).LowValue, TEnumType(A1.Typ).HighValue);
        typInt: Result := T;
        typBool: case TBoolType(A1.Typ).Kind of
            bolStd, bolByte: Result :=
                FContext.FByteType;
            bolWord: Result := FContext.FWordType;
            else
              Result := FContext.FLongWordType;
          end;
        typChar: if TCharType(A1.Typ).Kind = charAnsi then
            Result := FContext.FByteType
          else
            Result := FContext.FWordType;
        typSubrange: Result := GetUnderlineType(TSubrangeType(T).BaseType);
        else
          Result := FContext.FLongIntType;
      end;
    end;

    procedure CheckOrd;
    begin
      // ord parameter can be enum, int
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.IsOrdinal) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := GetUnderlineType(A1.Typ);
    end;

    procedure CheckPred;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.IsOrdinal) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := A1.Typ;
    end;

    procedure CheckPtr;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.IsInteger) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FPointerType;
    end;

    procedure CheckRound;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.TypeCode in [typInt, typNumeric]) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FInt64Type;
    end;

    procedure CheckSetLength;
    begin
      if Num > 1 then
      begin
        // A1 must be a variable
        if not ((A1.HasMemory) and (A1.Typ.TypeCode in [typString, typDynamicArray])) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
        // If it is a DynamicArray, the dimension must be checked
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FAnytype;
    end;

    procedure CheckSizeOf;
    begin
      // The SizeOf parameter can be any expression, and only calculate the size based on the type
    (* if Num = 1 then begin
       {if not (A1.NodeKind in [nkVariable, nkConstant, nkType, nkEnumElement, nkFunc, nkExpr]) then
           ParseError(A1.Coord, SErr_IncompatibleTypes);}
       end else
         ParseError(CallExpr.Coord, SErr_ArgNotMatched);*)
      if Num <> 1 then
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FIntegerType;
    end;

    procedure CheckSwap;
    begin
      if Num = 1 then
      begin
        NotAllowNode([nkType], A1);
        if not (A1.Typ.IsInteger) then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FWordType;
    end;

    procedure CheckTypeInfo;
    begin
      if Num = 1 then
      begin
        if not A1.IsTypeSymbol then
          ParseError(A1.Coord, SErr_IncompatibleTypes);
      end
      else
        ParseError(CallExpr.Coord, SErr_ArgNotMatched);
      Typ := FContext.FPointerType;
    end;

{    function createConst(Value: Integer): TConstExpr;
    begin
      Result := CreateConstExpr(opCONST);
      Result.Value := ValFromInt(Value);
    end;}
  begin
    ActualArgs := TListExpr(CallExpr.Right);
    Assert(ActualArgs.OpCode = opLIST);
    Num := ActualArgs.Count;
    A1 := nil;
    A2 := nil;
    A3 := nil;
    if Num > 0 then
      A1 := ActualArgs.Items[0];
    if Num > 1 then
      A2 := ActualArgs.Items[1];
    if Num > 2 then
      A3 := ActualArgs.Items[2];
    case Kind of
      bfAbs: CheckAbs;
      bfAddr: CheckAddr;
      bfAssigned: CheckAssigned;
      bfBreak, bfContinue: CheckBrCont;
      bfChr: CheckChr;
      bfCopy: CheckCopy;
      bfDispose: CheckDispose;
      bfDec, bfInc: CheckInc;
      bfExclude, bfInclude: CheckExclude;
      bfExit: CheckExit;
      bfFinalize, bfInitialize: CheckFinalize;
      bfFreeMem: CheckFreeMem;
      bfGetMem: CheckGetMem;
      bfHi, bfLo: CheckHi;
      bfHigh, bfLow: CheckHigh;
      bfLength: CheckLength;
      bfNew: CheckNew;
      bfOdd: CheckOdd;
      bfOrd: CheckOrd;
      bfPred, bfSucc: CheckPred;
      bfPtr: CheckPtr;
      bfRound, bfTrunc: CheckRound;
      bfSetLength: CheckSetLength;
      bfSizeOf: CheckSizeOf;
      bfSwap: CheckSwap;
      bfTypeInfo: CheckTypeInfo;
      else
        ParseError(CallExpr.Coord, 'Invalid builtin routine', True);
    end;
    if (Typ = FContext.FAnytype) and (CallExpr.Parent = nil) then
      Typ := FContext.FUntype;
    Result := CallExpr;
    // todo 999: If you add built-in functions, you need to check here
    // todo 1: Addr needs to be included
    if Kind in [bfAbs, bfChr, bfHi, bfHigh, bfLo, bfLow, bfOdd, bfOrd, bfPred, bfRound, bfSucc, bfSwap, bfTrunc] then
    begin
      if (A1 <> nil) and ((eaConst in A1.Attr) or A1.IsTypeSymbol) then
        Include(CallExpr.Attr, eaConst);
    end
    else if Kind in [bfSizeOf, bfLength] then
      Include(CallExpr.Attr, eaConst);
    if (eaConst in CallExpr.Attr) or ((Kind = bfAddr) and (psInConstExpr in Self.FCurStates) and
      not (psNotAllowAddr in Self.FCurStates)) then
    begin
      Result := ConstantFold(CallExpr);
    end;
  end;

  function ValueCastOk(typ: TType): boolean;
  begin
    Result := typ.IsOrdinal or (typ.TypeCode in [typPointer, typPAnsiChar, typPWideChar,
      typProcedural, typClass, typClassRef, typInterface]);
  end;

  {function VarCastOk(t1, t2: TType): Boolean;
   begin
     // Check if it can be varcast
     // int=>ptr,ptr=>int only the same size, but not regarded as VarCast
     // self=>ptr because Self is only a value
   end;}

  function CheckValueCast(L, R: TType): boolean;
  begin
    if L.TypeCode = typVariant then
      Result := R.IsOrdinal or R.IsReal or (R.TypeCode in [typInterface])
    else if R.TypeCode = typVariant then
      Result :=
        L.IsOrdinal or L.IsReal or (L.TypeCode in [typInterface])
    else if L.IsReal then // Int<=Real,Real<=Int, not allowed
      Result := {R.IsOrdinal or} R.IsReal
    else
      Result := ValueCastOk(L) and ValueCastOk(R);
  end;

  function CheckAdjustCall(E: TExpr): TExpr; forward;

  function CheckCast(bin: TBinaryExpr): TExpr;
  var
    L, R: TType;
    E: TExpr;
    HasMem, Ok: boolean;
  begin
    Result := bin;
    L := bin.Left.Typ.NormalType;
    E := bin.Right;
    bin.Typ := L;
    if E = nil then
    begin
      ParseError(bin.Coord, SErr_InvalidCast);
      Exit;
    end;
    EnsureNode(nkType, bin.Left);
    NotAllowNode([nkType], bin.Right);
    R := E.Typ.NormalType;
    HasMem := E.HasMemory;
    // see http://docwiki.embarcadero.com/RADStudio/en/Expressions_(Delphi)#Typecasts

     // todo 5: cast needs further study
     // todo 5: variable is also valid for properties and function return values TRec(obj.Prop)
     {
     ordinal type => ordinal type, pointer, variant, (set, array or record with memory of equal size)
     pointer type => ordinal type, pointer, string, class, classref, interface
     variant => ordinal, real, interface
      (set, array or record) => ordinal type, pointer with memory of equal size
     }
     {
       variable cast: The essence is to transform a piece of memory, which must be untyped or equal in size to the target type
                       And exclude Int<=>Real
       value cast: If it cannot be regarded as a variable cast, then it is a value cast
     }
    if HasMem and not (psInConstExpr in Self.FCurStates) then
    begin
      Ok := not (L.IsInteger and R.IsReal) and not (L.IsReal and R.IsInteger);
      if Ok then
      begin
        Ok := (L.Size = R.Size) or (R.TypeCode = typUntype);
        if not Ok then
          Ok := CheckValueCast(L, R)
        else  // 2016.3.26 For Int<=>Ptr of the same size, it is also regarded as a varcast
          Include(bin.Attr, eaVarCast);
        { else if not (L.IsInteger and R.IsPointerBased) and
              not (R.IsInteger and L.IsPointerBased) then // Ptr => Int or Int=>Ptr is not regarded as varcast
          Include(bin.Attr, eaVarCast);}
      end;
    end
    else
    begin
      Ok := CheckValueCast(L, R);
      {Ok := not (psInLeftVal in FCurStates);
      if Ok then
        Ok := CheckValueCast(L, R);}
    end;
    if Ok then
    begin
      if eaConst in E.Attr then
      begin
        Include(bin.Attr, eaConst);
        Result := ConstantFold(bin);
        //        bin := nil;
      end;
    end;
    if not Ok then
      ParseError(Result.Coord, SErr_InvalidCast)
    else
    begin
      // If the final result is a function, you should check whether a function call is made
      if Result.Typ.TypeCode = typProcedural then
        Result := CheckAdjustCall(Result);
    end;
  end;

  function CheckCall(bin: TBinaryExpr): TExpr;
  var
    L: TExpr;
    Typ: TType;
    Ref: ^TSymbol;
  begin
    {
     There are two situations for the left node of Call:
     1. Symbols
     2. Expressions that return function pointers
    }
    Result := bin;
    L := bin.Left;
    if L.OpCode = opMEMBER then
    begin
      {while TBinaryExpr(L).Right.OpCode = opMEMBER do
      begin
        L := TBinaryExpr(L).Right;
      end;}
      ASSERT(TBinaryExpr(L).Right.OpCode = opSYMBOL, 'CheckCall');
      Ref := @TSymbolExpr(TBinaryExpr(L).Right).reference;
    end
    else if L.OpCode = opSYMBOL then
      Ref := @TSymbolExpr(L).reference
    else
      Ref := nil;
    //    if (Ref = nil) then Exit;
    if (Ref <> nil) and (Ref^ <> nil) and (Ref^.NodeKind in [nkType, nkFunc, nkMethod,
      nkExternalFunc, nkBuiltinFunc]) then
    begin
      case Ref^.NodeKind of
        nkType:
        begin
          bin.OpCode := opCAST; // check type cast?
          Result := CheckCast(bin);
        end;
        nkFunc, nkMethod, nkExternalFunc:
        begin
          CheckArgs(TFunctionDecl(Ref^), bin);
          bin.Typ := TFunctionDecl(Ref^).ReturnType;
          if bin.Typ = nil then
            if bin.Parent <> nil then
              bin.Typ := FContext.FAnytype
            else
              bin.Typ := FContext.FUntype;
        end;
        nkBuiltinFunc:
        begin
          Typ := nil;
          Result := CheckBuiltinArgs(TBuiltinFunction(Ref^).Kind, bin, Typ);
          if Result = bin then
            bin.Typ := Typ;
          TSymbolExpr(L).Typ := Typ;
        end;
        else
          ParseError(bin.Coord, SErr_InvalidOperand);
      end;
    end
    else if (L.Typ.IsProcedural) then
    begin // variable of procedural?
      NotAllowNode([nkType], L);
      CheckArgs(TProceduralType(L.Typ).Params, bin);
      bin.Typ := TProceduralType(L.Typ).ReturnType;
      if bin.Typ = nil then
      begin
        if bin.Parent = nil then
          bin.Typ := FContext.FUntype
        else
          bin.
            Typ := FContext.FAnytype;
      end;
    end
    else
      ParseError(bin.Coord, SErr_InvalidOperand);
  end;

  // Check if there is an @ operation before the expression
  function AddrOpPrefix(E: TExpr): boolean;
  begin
    Result := (E.Parent <> nil) and (E.Parent.OpCode = opADDR);
    {
     // todo 1: This is not appropriate. For example @obj[proc1].show, judge proc1 to be invalid
     Result := True;
     E := E.Parent;
     while E <> nil do
     begin
       if E.OpCode = opADDR then Exit;
       E := E.Parent;
     end;
     Result := False;}
  end;

type
  TCallNeedCheckResult = (cncrNeed, cncrDelayed, cncrIsCall, cncrIsAddr, cncrOther);

  // Check whether the expression E needs to be expanded to call, and return cncrNeed as needed
  // E is TSymbolExpr or opMember or TExpr of type TProceduralType
  // Ref is the symbol pointed to by E, which can be nil
  // FunT is the type of E, which can be nil
  function CallNeedCheck(E: TExpr; Ref: TSymbol; FunT: TProceduralType): TCallNeedCheckResult;
  var
    T: TType;
    isFun: boolean;
  begin
    if psInAccessor in FCurStates then
    begin
      Result :=
        cncrOther;
      Exit;
    end;
    if synProcvarFpc in FSyntaxOptions then
    begin
      // The fpc style syntax does not need to be dynamically judged based on the location of the symbol.
      // Function: call.
      // Function variable: variable.
      // Take function pointer: add @
      isFun := (Ref <> nil) and (Ref.NodeKind in [nkFunc, nkMethod, nkExternalFunc]);
      if isFun then
      begin
        if Assigned(E.Parent) then
        begin
          case E.Parent.OpCode of
            opADDR: Result := cncrIsAddr;
            opCALL, opINHERITED: Result := cncrIsCall;
            // todo 1: opINHERITED?
            else
              Result := cncrNeed;
          end;
        end
        else
          Result := cncrNeed;
      end
      else
        Result := cncrOther;
      Exit;
    end;
    if E.Parent = nil then
    begin
      if psInLeftVal in FCurStates then
      begin
        if (Ref <> nil) and (Ref.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) then
          Result := cncrNeed  // function cannot be assigned
        else
          Result := cncrOther;  // At this time, it is impossible to decide whether it is a function call. Wait for further analysis
      end
      else if FExpectedProcType then
        Result := cncrOther
      else
        Result := cncrNeed;
    end
    else if E.Parent.OpCode in [opCALL, opINHERITED] then
      Result := cncrIsCall   // Already Call
    else if AddrOpPrefix(E) then
      Result := cncrIsAddr   // take address
    else
    begin
      if (Ref <> nil) and (Ref.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) then
        T := TFunctionDecl(Ref).ReturnType
      else if FunT <> nil then
        T := FunT.ReturnType
      else
        T := nil;
      // 1. There is a return value 2. The parent is the parameter list
      if (T <> nil) and (eaArgList in E.Parent.Attr) then
      begin
        Result := cncrDelayed;
      end
      else if (Ref.NodeKind in [nkVariable, nkFuncParam, nkField]) and (E.Parent.OpCode = opCAST) then
        Result := cncrOther
      else if T <> nil then
        Result := cncrNeed
      else
        Result := cncrOther;
    end;
  end;

  // Determine whether the expression E needs to be expanded to call. Return true to indicate the need
  // If you need to delay the judgment, the Attr marked E is eaDelayed
  // E is TSymbolExpr or TExpr of type TProceduralType
  // Ref is the symbol pointed to by E, which can be nil
  // FunT is the type of E, which can be nil
  function IsCallNeed(E: TExpr; Ref: TSymbol; FunT: TProceduralType): boolean;
  begin
    case CallNeedCheck(E, Ref, FunT) of
      cncrDelayed:
      begin
        Include(E.Attr, eaDelayed); // Go to the parent to decide whether to call
        Result := False;
      end;
      cncrNeed: Result := True;
      else
        Result := False;
    end;
  end;

  // Check and create opCALL expression
  // Parameter E is an expression that returns TProceduralType, not a function symbol
  function CheckAdjustCall(E: TExpr): TExpr;
  begin
    Result := nil;
    if E.Typ.TypeCode <> typProcedural then
      Exit;
    //  Assert(E.Typ.TypeCode = typProcedural, 'CheckAdjustCall');
    if IsCallNeed(E, nil, TProceduralType(E.Typ)) then
    begin
      Result := CreateCallExpr(E);
      CheckCall(TBinaryExpr(Result));
    end;
  end;

  procedure CheckVisibility(Sym: TSymbol);
  var
    IsVis: boolean;
    F: TSymbol;
  begin
    if FCurFunction <> nil then
    begin
    (*// Find top-level functions
      F := Parser.FCurFunction;
      while (F.Parent <> nil) and
        (F.Parent.NodeKind in [nkFunc, nkMethod]) do
      begin
        F := TFunction(F.Parent);
      end; *)
      F := FTopFunction;
      IsVis := Self.IsVisible(F, Sym);
    end
    else
      IsVis := Self.IsVisible(FCurParent, Sym);
    if not IsVis then
      ParseError(SErr_SymbolNotAccess, [Sym.Name]);
  end;

  {Check if the member can access}
  function CanMemberAccess(Ref: TSymbol): boolean;
  var
    P1, P2: TType;
  begin
    // If Ref is a field, attribute, or method, you need to check whether it is a member of the class where the current method is located.
    if Assigned(FTopFunction) and (Ref.NodeKind in [nkMethod, nkField, nkProperty, nkIntfProperty]) and
      not (saStatic in Ref.Attr) and not (saClass in Ref.Attr) then
    begin
      if (FTopFunction.NodeKind <> nkMethod) or (FTopFunction.Parent = nil) or (Ref.Parent = nil) or
        (FTopFunction.Parent.NodeKind <> nkType) or (Ref.Parent.NodeKind <> nkType) then
      begin
        Result := False;
        Exit;
      end;
      P1 := TType(FTopFunction.Parent);
      P2 := TType(Ref.Parent);
      Result := P1 = P2;
      if not Result and (P1.TypeCode = P2.TypeCode) then
      begin
        case P1.TypeCode of
          typClass: Result := TClassType(P1).IsInheritedFrom(TClassType(P2));
          typObject: Result := TObjectType(P1).IsInheritedFrom(TObjectType(P2));
          else
            Result := False;
        end;
      end;
    end
    else
      Result := True;
  end;

  // Check the symbol, if this symbol is a function, an expression of opCALl may be created
  function CheckSymbol(sym: TSymbolExpr): TExpr;
  var
    Ref: TSymbol;
  begin
    Result := sym;
    if sym.reference <> nil then
      Ref := sym.reference
    else
      Ref := FindSymbol(sym.Name);
    if Ref = nil then
      ParseError(sym.Coord, SErr_UndeclaredIdent, [sym.Name])
    else
    begin
      Include(Ref.Attr, saUsed);
      if (Ref.Parent = nil) and (Ref.NodeKind <> nkModule) then
        ParseError(SErr_InternalError, ['CheckSymbol:Parent=nil'], True);
      CheckVisibility(Ref);
      sym.reference := Ref;
      case Ref.NodeKind of
        // nkNameScope: sym.Typ := TNameScope(E).GetType;
        // nkModule: sym.Typ := TModule(E).GetType;
        // Because NameScope and Module have been removed in ParseExpr, they will not appear here
        nkNameScope,
        nkModule: Assert(False, 'NameScope and Module should not be occurred');
        nkType: sym.Typ := TType(Ref);
        // Var, const, arg, field, if the type is procedure, you need to check whether it is a function call or as a variable
        nkVariable, nkFuncParam, nkConstant, nkField, nkProperty, nkIntfProperty:
        begin
          case Ref.NodeKind of
            nkVariable: Sym.Typ := TVariable(Ref).VarType;
            nkFuncParam: Sym.Typ := TFuncParam(Ref).ParamType;
            nkConstant: Sym.Typ := TConstant(Ref).ConstType;
            nkField: Sym.Typ := TField(Ref).FieldType;
            nkProperty: Sym.Typ := TProperty(Ref).PropType;
            nkIntfProperty: Sym.Typ := TIntfProperty(Ref).PropType;
          end;
          if Sym.Typ = nil then
            Sym.
              Typ := FContext.FUntype;
          if Ref.NodeKind = nkConstant then
            Include(Sym.Attr, eaConst);
          if not CanMemberAccess(Ref) then
            ParseError('Can not access Outter''s non-static member: %s', [Sym.Name]);
          if FCurFunction <> nil then
          begin
            case Ref.NodeKind of
              nkVariable: if (FCurFunction.Level > TVariable(Ref).Level)
                          and (vaLocal in TVariable(Ref).VarAttr)
                          {and (TVariable(Ref).Level > 0)} then
                begin
                  Include(TVariable(Ref).States, vsNestRef);
                  Include(FCurFunction.FuncAttr, faNeedFPArg);
                end;
              nkFuncParam: if (FCurFunction.Level > TFuncParam(Ref).Level)
                          {and (TFuncParam(Ref).Level > 0)} then
                begin
                  Include(TFuncParam(Ref).States, asNestRef);
                  Include(FCurFunction.FuncAttr, faNeedFPArg);
                end;
            end;
          end;
          if Sym.Typ.TypeCode = typProcedural then
            if IsCallNeed(Sym, Ref, TProceduralType(Sym.Typ)) then
            begin
              Result := CreateCallExpr(Sym);
              CheckCall(TBinaryExpr(Result));
            end;
        end;
        nkEnumElement:
        begin
          sym.Typ := TEnumValue(Ref).EnumType;
          Include(Sym.Attr, eaConst);
        end;
        nkExternalFunc, nkFunc, nkMethod:
        begin
          if not CanMemberAccess(Ref) then
            ParseError('Can not access Outter''s non-static member: %s', [Sym.Name]);
          Sym.Typ := FContext.FUntype;
          case CallNeedCheck(Sym, Ref, nil) of
            cncrNeed:
            begin
              Result := CreateCallExpr(Sym);
              CheckCall(TBinaryExpr(Result));
              // Ref is a nested function, the nesting level is not greater than the current function
              if (FCurFunction <> nil) and (Ref.NodeKind = nkFunc) and (TFunction(Ref).Level > 0) and
                (TFunction(Ref).Level <= FCurFunction.Level) then
              begin
                Include(FCurFunction.FuncAttr, faNeedFPArg);
              end;
            end;
            cncrDelayed: Include(Sym.Attr, eaDelayed);
            cncrOther:
            begin
              // It has been ensured that Ref.NodeKind in [nkMethod, nkFunc, nkExternalFunc]
              // To take a function pointer, you need to use @
              Sym.Typ := TFunctionDecl(Ref).ProceduralType;
              Result := CreateProcAddrExpr(Sym);
            end;
            else
              Sym.Typ := TFunctionDecl(Ref).ProceduralType;
          end;
        end;
        nkBuiltinFunc:
        begin
          Sym.Typ := FContext.FUntype;
          if (Sym.Parent = nil) or (Sym.Parent.OpCode <> opCALL) then
          begin
            Result := CreateCallExpr(Sym);
            CheckCall(TBinaryExpr(Result));
          end;
        end;
        else
          ParseError(Sym.Coord, 'Unknown type of Identifier', True);
      end;
    end;
    if Sym.Typ = nil then
      Sym.Typ := FContext.FAnytype;
    if (Result <> nil) and (Result.Typ = nil) then
      Result.Typ := Sym.Typ;
  end;

  function CheckInst(un: TUnaryExpr): TExpr; forward;

  function CheckSubSymbol(bin: TBinaryExpr): TExpr;  // opMEMBER

    procedure TryAddInstOp;
    var
      typ: TPointerType;
      InstE: TUnaryExpr;
      L: TExpr;
    begin
      typ := TPointerType(bin.Left.Typ);
      if (typ.RefType <> nil) and (typ.RefType.TypeCode in [typRecord, typObject]) then
      begin
        L :=
          bin.Left;
        L.Detach;
        InstE := CreateUnaryExpr(opINST, L);
        InstE.Coord := InstE.Operand.Coord;
        CheckInst(InstE);
        bin.Left := InstE;
      end;
    end;

    function IsConstructor(Ref: TSymbol): boolean;
    begin
      Result := (Ref.NodeKind = nkMethod) and (TMethod(Ref).MethodKind = mkConstructor);
    end;

  var
    Ref: TSymbol;
    Sym: TSymbolExpr;
  begin
    Result := bin;
    if bin.Right.OpCode <> opSYMBOL then
    begin
      ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FAnytype;
      Exit;
    end;
    Sym := TSymbolExpr(bin.Right);
    Ref := Sym.reference;
    if Ref = nil then
    begin
      if bin.Left.Typ.TypeCode = typPointer then
      begin
        TryAddInstOp;
      end;
      case bin.Left.Typ.TypeCode of
      // Because NameScope and Module have been removed in ParseExpr, they will not appear here
      {  typSymbol: begin
          Ref := TSymbolExpr(bin.Left).Reference;
          if Ref.NodeKind = nkNameScope then
            Ref := TNameScope(Ref).FindSymbol(Sym.Name)
          else if Ref.NodeKind = nkModule then
            Ref := TModule(Ref).FindSymbol(Sym.Name)
          else
            Ref := nil;
        end;}
        {
        typPointer: begin
          NotAllowNode([nkType], bin.Left);
          Ref := CheckRecPtr(TPointerType(bin.Left.Typ), Sym);
        end;}
        typRecord:
        begin
          Ref := TRecordType(bin.Left.Typ).FindSymbol(Sym.Name);
          if bin.Left.IsTypeSymbol then
          begin
            if ([saStatic, saClass] * Ref.Attr = []) and (Ref.NodeKind <> nkConstant) then
              ParseError(bin.Coord, SErr_SymbolNotClassOrStatic, [Sym.Name]);
          end
          else if (saStatic in Ref.Attr) then
            DoWarning(bin.Coord, SWarn_SymbolThroughInstance, [Sym.Name]);
        end;
        typClass:
        begin
          Ref := TClassType(bin.Left.Typ).FindSymbol(Sym.Name);
          if bin.Left.IsTypeSymbol then
          begin
            if ([saStatic, saClass] * Ref.Attr = []) and (Ref.NodeKind <> nkConstant) and not IsConstructor(Ref) then
              ParseError(bin.Coord, SErr_SymbolNotClassOrStatic, [Sym.Name]);
          end
          else if (saStatic in Ref.Attr) then
            DoWarning(bin.Coord, SWarn_SymbolThroughInstance, [Sym.Name]);
        end;
        typClassRef:
        begin
          Ref := TClassRefType(bin.Left.Typ).RefType.FindSymbol(Sym.Name);
          if ([saStatic, saClass] * Ref.Attr = []) and (Ref.NodeKind <> nkConstant) and not IsConstructor(Ref) then
            ParseError(bin.Coord, SErr_SymbolNotClassOrStatic, [Sym.Name]);
        end;
        typObject:
        begin
          Ref := TObjectType(bin.Left.Typ).FindSymbol(Sym.Name);
          if bin.Left.IsTypeSymbol then
          begin
            if ([saStatic, saClass] * Ref.Attr = []) and (Ref.NodeKind <> nkConstant) then
              ParseError(bin.Coord, SErr_SymbolNotClassOrStatic, [Sym.Name]);
          end
          else if (saStatic in Ref.Attr) then
            DoWarning(bin.Coord, SWarn_SymbolThroughInstance, [Sym.Name]);
        end;
        typInterface: Ref := TInterfaceType(bin.Left.Typ).FindSymbol(Sym.Name);
        // todo 5: helper class will be added later
        else
          ParseError(bin.Coord, SErr_InvalidOperand);
      end;
    end;
    if Ref = nil then
    begin
      ParseError(bin.Coord, SErr_UndeclaredIdent, [Sym.Name]);
      Sym.Typ := FContext.FAnytype;
    end
    else
    begin
      Sym.reference := Ref;
      // Because NameScope and Module have been removed in ParseExpr, they will not appear here
      if Ref.NodeKind in [nkNameScope, nkModule] then
        ParseError(bin.Coord, SErr_InvalidIdent, [Ref.Name]);
      CheckVisibility(Ref);
      case Ref.NodeKind of
        nkType: Sym.Typ := TType(Ref);
        nkVariable, nkFuncParam, nkConstant, nkField, nkProperty, nkIntfProperty:
        begin
          case Ref.NodeKind of
            nkVariable: Sym.Typ := TVariable(Ref).VarType;
            nkFuncParam: Sym.Typ := TFuncParam(Ref).ParamType;
            nkConstant: Sym.Typ := TConstant(Ref).ConstType;
            nkField: Sym.Typ := TField(Ref).FieldType;
            nkProperty: Sym.Typ := TProperty(Ref).PropType;
            nkIntfProperty: Sym.Typ := TIntfProperty(Ref).PropType;
          end;
          if Ref.NodeKind = nkConstant then
            Include(Sym.Attr, eaConst);
          if Sym.Typ.TypeCode = typProcedural then
            if IsCallNeed(bin, Ref, TProceduralType(Sym.Typ)) then
            begin
              Result := CreateCallExpr(bin);
              CheckCall(TBinaryExpr(Result));
            end;
        end;
        nkEnumElement:
        begin
          Sym.Typ := TEnumValue(Ref).EnumType;
          Include(Sym.Attr, eaConst);
        end;
        nkFunc, nkMethod, nkExternalFunc:
        begin
          Sym.Typ := FContext.FUntype;
          case CallNeedCheck(bin, Ref, nil) of
            cncrNeed:
            begin
              Result := CreateCallExpr(bin);
              CheckCall(TBinaryExpr(Result));
            end;
            cncrDelayed: Include(bin.Attr, eaDelayed);
            cncrOther:
            begin
              // It has been ensured that Ref.NodeKind in [nkMethod, nkFunc, nkExternalFunc]
              // To take a function pointer, you need to use @
              Sym.Typ := TFunctionDecl(Ref).ProceduralType;
              bin.Typ := Sym.Typ;
              Result := CreateProcAddrExpr(bin);
            end;
            else
              Sym.Typ := TFunctionDecl(Ref).ProceduralType;
          end;
        end;
        nkBuiltinFunc:
        begin
          Sym.Typ := FContext.FUntype;
          if Sym.Parent.OpCode <> opCALL then
            CheckCall(CreateCallExpr(Sym));
        end;
        else
          ParseError(Sym.Coord, 'Unknown type of Identifier');
      end;
      if Sym.Typ = nil then
        Sym.Typ := FContext.FAnytype;
    end;
    if bin <> nil then
    begin
      bin.Typ := Sym.Typ;
      if eaConst in Sym.Attr then
        Include(bin.Attr, eaConst);
    end;
  end;

  function CheckInst(un: TUnaryExpr): TExpr;
  var
    Typ: TType;
  begin
    Result := un;
    NotAllowNode([nkType], un.Operand);
    Typ := un.Operand.Typ;
    case Typ.TypeCode of
      typPointer:
      begin
        if TPointerType(Typ).RefType <> nil then
          un.Typ := TPointerType(Typ).RefType
        else
          un.Typ := FContext.FUntype;
        if un.Typ.TypeCode = typProcedural then
          Result := CheckAdjustCall(un);
      end;
      typPAnsiChar: un.Typ := FContext.FAnsiCharType;
      typPWideChar: un.Typ := FContext.FWideCharType;
      else
        ParseError(un.Coord, SErr_InvalidOperand);
    end;
  end;

  // The left side must be the same type as the right side
  procedure CheckRange(bin: TBinaryExpr);
  var
    L, R: TType;
  begin
    NotAllowNode([nkType], bin.Left);
    NotAllowNode([nkType], bin.Right);
    L := bin.Left.Typ;
    R := bin.Right.Typ;
    if L.TypeCode = typSubrange then
      L := TSubrangeType(L).BaseType;
    if R.TypeCode = typSubrange then
      R := TSubrangeType(R).BaseType;
    if L.IsInteger then
    begin
      if not R.IsInteger then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.
        Typ := L;
    end
    else if L.IsBoolean then
    begin
      if not R.IsBoolean then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := FContext.FBooleanType;
    end
    else if L.TypeCode = typChar then
    begin
      if R.TypeCode <> typChar then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := L;
    end
    else if L.TypeCode = typEnum then
    begin
      if R <> L then
        ParseError(bin.Coord, SErr_InvalidOperand);
      bin.Typ := L;
    end
    else
    begin
      bin.Typ := FContext.FIntegerType;
      ParseError(bin.Coord, SErr_InvalidOperand);
    end;
    if (eaConst in bin.Left.Attr) and (eaConst in bin.Right.Attr) then
      Include(bin.Attr, eaConst);
  end;

  procedure CheckIndexProperty(bin: TBinaryExpr; Ref: TSymbol);
  var
    Args: TFuncParamList;
  begin
    case Ref.NodeKind of
      nkProperty:
      begin
        Args := TProperty(Ref).Params;
        bin.Typ := TProperty(Ref).PropType;
      end;
      nkIntfProperty:
      begin
        Args := TIntfProperty(Ref).Params;
        bin.Typ := TIntfProperty(Ref).PropType;
      end;
      else
        Args := nil;
    end;
    CheckArgs(Args, bin);
  end;

  procedure CheckDefaultProperty(bin: TBinaryExpr; Ref: TSymbol);
  var
    LTyp: TType;
    DefProp: TSymbol;
    NewL: TBinaryExpr;
    PropExpr: TSymbolExpr;
  begin
    LTyp := bin.Left.Typ;
    case LTyp.TypeCode of
      typClass: DefProp := TClassType(LTyp).DefaultProp;
      typInterface: DefProp := TInterfaceType(LTyp).DefaultProp;
      else
        Exit;
    end;
    PropExpr := CreateSymbolExpr(DefProp.Name);
    PropExpr.reference := DefProp;
    PropExpr.Coord := bin.Coord;
    NewL := CreateBinaryExpr(opMEMBER, bin.Left, PropExpr);
    bin.Left := NewL;
    NewL.Coord := bin.Coord;
    CheckSubSymbol(NewL);
    CheckIndexProperty(bin, DefProp);
  end;

  {
  function CheckIndexType(Typ: TType; E: TExpr): Boolean;
    function CheckRangeType(t1, t2: TType): Boolean;
    begin
      if t1.TypeCode = typSubrange then t1 := TSubrangeType(t1).BaseType;
      if t2.TypeCode = typSubrange then t2 := TSubrangeType(t2).BaseType;
      case t1.TypeCode of
        typEnum: Result := t1 = t2;
        typInt:
          Result := t2.TypeCode in [typInt, typVariant];
        typVariant:
          Result := True;
      else
        Result := t1.TypeCode = typ.TypeCode;
      end;
    end;
  begin
    if Typ = nil then
    begin
      Parser.ParseError(E.Coord, SErr_ArrayRequired);
      Result := False;
      Exit;
    end;
    Result := True;
    case Typ.TypeCode of
      typAnsiString..typShortString,
      typPAnsiChar, typPWideChar:
        if not E.Typ.IsInteger then
          Parser.ParseError(E.Coord, SErr_IncompatibleTypes);
      typDynamicArray:
        if not E.Typ.IsInteger then
          Parser.ParseError(E.Coord, SErr_IncompatibleTypes);
      typArray:
        if not CheckRangeType(E.Typ, TArrayType(Typ).Range) then
          Parser.ParseError(E.Coord, SErr_IncompatibleTypes);
    else
      Parser.ParseError(E.Coord, SErr_ArrayRequired);
      Result := False;
    end;
  end;  }

  // check this dimension
  function CheckIndexType(var Typ: TType; E: TExpr): boolean;

    function CheckIndiceType(t1, t2: TType): boolean;
    begin
      // t1: the type to be checked, t2: the expected type
      if t1.TypeCode = typSubrange then
        t1 := TSubrangeType(t1).BaseType;
      if t2.TypeCode = typSubrange then
        t2 := TSubrangeType(t2).BaseType;
      case t1.TypeCode of
        typEnum: Result := t1 = t2;
        typInt: Result := t2.TypeCode in [typInt, typVariant];
        typVariant: Result := True;
        else
          Result := t1.TypeCode = typ.TypeCode;
      end;
    end;

  var
    ElemTyp: TType;
  begin
    if Typ = nil then
    begin
      ParseError(E.Coord, SErr_ArrayRequired);
      Result := False;
      Exit;
    end;
    Result := True;
    case Typ.TypeCode of
      typString:
      begin
        if TStringType(Typ).Kind in [strAnsi, strAShort] then
          ElemTyp := FContext.FAnsiCharType
        else
          ElemTyp := FContext.FWideCharType;
        if not CheckIndiceType(E.Typ, FContext.FLongIntType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typPAnsiChar:
      begin
        ElemTyp := FContext.FAnsiCharType;
        if not CheckIndiceType(E.Typ, FContext.FLongIntType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typPWideChar:
      begin
        ElemTyp := FContext.FWideCharType;
        if not CheckIndiceType(E.Typ, FContext.FLongIntType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typPointer:
      begin
        if Typ.IsUntypePointer then
          ParseError(E.Coord, SErr_ArrayRequired);
        ElemTyp := TPointerType(Typ).RefType;
        if ElemTyp = nil then
          ElemTyp := FContext.FUntype;
        if not CheckIndiceType(E.Typ, FContext.FLongIntType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typDynamicArray:
      begin
        ElemTyp := TDynamicArrayType(Typ).ElementType;
        if not CheckIndiceType(E.Typ, FContext.FLongIntType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typArray:
      begin
        ElemTyp := TArrayType(Typ).ElementType;
        if not CheckIndiceType(E.Typ, TArrayType(Typ).Range) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typOpenArray:
      begin
        ElemTyp := TOpenArrayType(Typ).ElementType;
        WriteLn('typOpenArray: ', ElemTyp.FullName);
        if not CheckIndiceType(E.Typ, TOpenArrayType(Typ).ElementType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      typVariant:
      begin
        ElemTyp := FContext.FVariantType;
        if not CheckIndiceType(E.Typ, FContext.FLongIntType) then
          ParseError(E.Coord, SErr_IncompatibleTypes);
      end;
      else
      begin
        ParseError(E.Coord, SErr_ArrayRequired);
        ElemTyp := nil;
        Result := False;
      end;
    end;
    if ElemTyp <> nil then
      Typ := ElemTyp;
  end;

  function CheckIndex(bin: TBinaryExpr): TExpr;
  var
    E: TExpr;
    List: TListExpr;
    I: integer;
    Typ: TType;
    Ref: TSymbol;
    IsArrayProp, IsDefProp: boolean;
  begin
    Result := bin;
    List := TListExpr(bin.Right);
    if List.Count = 0 then
    begin
      ParseError(bin.Coord, SErr_ExpectExpression);
      Exit;
    end;
    NotAllowNode([nkType], bin.Left);
    Ref := bin.Left.GetReference;
    {Consider this situation:
       obj.Symbols[i];
       If Symbols is an Array Property, then IsArrayProp=True
       If Symbols is a class, and this class has default properties, then IsDefProp=True
     }
    IsArrayProp := False;
    IsDefProp := False;
    if Ref <> nil then
      case Ref.NodeKind of
        nkProperty: IsArrayProp := TProperty(Ref).ParamCount > 0;
        nkIntfProperty: IsArrayProp := TIntfProperty(Ref).ParamCount > 0;
      end;
    if not IsArrayProp then
      case bin.Left.Typ.TypeCode of
        typClass: IsDefProp := TClassType(bin.Left.Typ).DefaultProp <> nil;
        typInterface: IsDefProp := TInterfaceType(bin.Left.Typ).DefaultProp <> nil;
      end;
    if IsArrayProp or IsDefProp then
      Include(bin.Attr, eaArrayProp);
    if IsArrayProp then
    begin
      CheckIndexProperty(bin, Ref);
    end
    else if IsDefProp then
    begin
      // Switch to access to the default attributes and check
      CheckDefaultProperty(bin, Ref);
    end
    else
    begin
      E := List.Items[0];
      case bin.Left.Typ.TypeCode of
        typString, typPAnsiChar, typPWideChar:
        begin
          if List.Count > 1 then
            ParseError(bin.Coord, SErr_ArrayRequired);
          Typ := bin.Left.Typ;
          CheckIndexType(Typ, E);
          bin.Typ := Typ;
        end;
        typArray, typDynamicArray, typOpenArray, typPointer:
        begin
          Typ := bin.Left.Typ;
          I := 0;
          repeat
            if not CheckIndexType(Typ, E) then
              Break;
            bin.Typ := Typ;
            Inc(I);
            E := List.Items[I];
          until (I >= List.Count) or (Typ = nil);
        end;
        else
          if bin.Left.Typ.TypeCode in [typClass, typInterface] then
            ParseError(bin.Coord, SErr_NoDefaultProp)
          else
            ParseError(bin.Coord, SErr_ArrayRequired);
          bin.Typ := FContext.FAnytype;
      end;
      if bin.Typ.TypeCode = typVariant then
        Include(bin.Attr, eaVarOp);
    end;
    // If this Property returns a process variable, it should be checked whether it is converted to a call
    // Such as: Ctrl.OnClick[1];
    // Ctrl.OnClick;
    // Ctrl.Procs[1];
    if bin.Typ.TypeCode = typProcedural then
      Result := CheckAdjustCall(bin);
  end;

  procedure NormalAddrOp(un: TUnaryExpr);
  begin
    // Adjust the pointer type according to the state of $T+
    if FTypedAddress then
    begin
      if un.Operand.Typ.TypeCode = typUntype then
        un.Typ := FContext.FPointerType
      else
      begin
        un.Operand.Typ.CreatePointerType(FPointerSize);
        un.Typ := un.Operand.Typ.PointerType;
      end;
    end
    else
      un.Typ := FContext.FPointerType;
  end;

  function CheckDblAddrOp(un: TUnaryExpr): TExpr;
  begin
    if not (un.HasMemory and un.Operand.Typ.IsProcedural) then
      ParseError(un.Coord, SErr_InvalidOperand);
    un.OpCode := opADDR;
    NormalAddrOp(un);
    if (psInConstExpr in FCurStates) and not (psNotAllowAddr in FCurStates) then
    begin
      Result := ConstantFold(un);
    end;
  end;

  function CheckAddrOp(un: TUnaryExpr):
  TExpr;
  var
    Func: TFunctionDecl;
    Ref: TSymbol;
  begin
    {On the @@ operator on function pointers. There is no need to keep two @nodes here.
       AST means that the call and address are already clear
     }
    Result := un;
    if not (un.Operand.HasMemory or un.Operand.IsFunction) then
    begin
      ParseError(un.Coord, SErr_InvalidOperand);
      un.Typ := FContext.FPointerType;
      Exit;
    end;
    Ref := un.Operand.GetReference;
    // Cannot use @ for Self
    if (Ref <> nil) and (Ref.NodeKind = nkVariable) and (vaSelf in TVariable(Ref).VarAttr) then
    begin
      ParseError(un.Coord, SErr_InvalidOperand);
      un.Typ := FContext.FPointerType;
      Exit;
    end;
    if Assigned(Ref) and (Ref.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) then
      Func := TFunctionDecl(Ref)
    else
      Func := nil;
    if (Func <> nil) then
    begin
      // @proc takes the function/method address, the final type of fpc is TProceduralType
      // delphi is TPointerType. And does not accept @obj.method this form
      if synProcvarFpc in FSyntaxOptions then
      begin
        un.Typ := Func.ProceduralType;
      end
      else
      begin
        un.Typ := FContext.FPointerType;
        // todo 1: If operand is not referenced by a class name like tobject.classinfo, an error will be reported
      end;
      if Func.IsOverload then
        Include(un.Attr, eaDelayed);
    end
    else if un.Operand.Typ.TypeCode = typProcedural then
    begin
      // For @procvar, fpc is interpreted as taking the variable address
      if synProcvarFpc in FSyntaxOptions then
        NormalAddrOp(un)
      else
      begin
        // Take the value stored in the variable. Remove the @ operator
        Result := un.Operand;
        Result.Detach;
        if Result.Typ = nil then
          Result.Typ := FContext.FPointerType;
        SubstituteExpr(un, Result);
        //  SubstituteExpr(un, un.Operand);
        Self.ReleaseExpr(un);
        un := nil;
      end;
    end
    else
    begin
      NormalAddrOp(un);
    end;
    if (un <> nil) and (psInConstExpr in FCurStates) and not (psNotAllowAddr in FCurStates) then
    begin
      Result := ConstantFold(un);
    end;
  end;

  function CheckInherited(E: TUnaryExpr): TExpr;

    function GetBaseSymbol(const s: TSymString): TSymbol;
    var
      parent: TSymbol;
    begin
      Result := nil;
      parent := FTopFunction.Parent;
      if parent.NodeKind <> nkType then
        Exit;
      case
        TType(parent).TypeCode of
        typClass: Result := TClassType(parent).FindBaseSymbol(S);
        typObject: Result := TObjectType(parent).FindBaseSymbol(S);
      end;
    end;

  var
    Sym: TSymbol;
    CallE: TBinaryExpr;
    SymE: TSymbolExpr;
    i: integer;
  begin
    Result := E;
    // Must be in a method or its nested function.
    // The method called must be owned by the base class.
    if (FTopFunction = nil) or (FTopFunction.NodeKind <> nkMethod) then
    begin
      ParseError(E.Coord, SErr_InheritedNotAllow);
      Exit;
    end;
    {Several formats:
       inherited; // ok A single inherited, which means to call the method of the same name of the base class.
       inherited docheck; // ok calls the specified method of the base class
       result := inherited docheck; // ok is placed in the expression
       result := inherited prop // ok property
       result := inherited; // error inherited in the expression must take identifiers and parameters
     }
    if E.Operand = nil then
    begin
      Sym := GetBaseSymbol(FTopFunction.Name);
      if Sym = nil then
      begin
        // inherited cannot omit the called method identifier in the expression
        if E.Parent <> nil then
          ParseError(E.Coord, SErr_InheritedExpectId)
        else
        begin
          // If the base class does not have a method with the same name, and it is not in an expression, ignore this sentence.
          // Create an air conditioner  // Probably wrong translation, this is the original Chinese text: // 创建一个空调用
          CallE := CreateBinaryExpr(opCALL);
          CallE.Coord := E.Coord;
          CallE.Typ := FContext.FUntype;
          CallE.Left := CreateSymbolExpr(FContext.FNoopFunc.Name);
          TSymbolExpr(CallE.Left).reference := FContext.FNoopFunc;
          CallE.Left.Typ := FContext.FUntype;
          CallE.Left.Coord := E.Coord;
          CallE.Right := CreateListExpr;
          CallE.Right.Coord := E.Coord;
          CallE.Right.Typ := FContext.FUntype;
          Self.ReleaseExpr(E);
          Result := CallE;
        end;
        Exit;
      end
      else if Sym.NodeKind <> nkMethod then
      begin
        ParseError(
          E.Coord, SErr_IncompatibleTypes);
        Exit;
      end;
      CallE := CreateBinaryExpr(opCALL);
      CallE.Coord := E.Coord;
      Include(CallE.Attr, eaInherited);
      CallE.Left := CreateSymbolExpr(Sym.Name);
      TSymbolExpr(CallE.Left).reference := Sym;
      CallE.Left.Typ := FContext.FUntype;
      CallE.Left.Coord := E.Coord;
      Include(CallE.Left.Attr, eaInherited);
      CallE.Right := CreateListExpr;
      CallE.Right.Typ := FContext.FUntype;
      CallE.Right.Coord := E.Coord;
      // copy args
      for i := 0 to FTopFunction.ParamCount - 1 do
      begin
        SymE := CreateSymbolExpr(FTopFunction.Params[i].Name);
        SymE.Coord := E.Coord;
        SymE.reference := FTopFunction.Params[i];
        TListExpr(CallE.Right).Add(symE);
      end;
      SubstituteExpr(E, CallE);
      Self.ReleaseExpr(E);
      CheckCall(CallE);
      Result := CallE;
    end
    else
    begin
      Assert(E.Operand.OpCode = opSYMBOL, 'CheckInherited: Expected left only symbol');
      Sym := GetBaseSymbol(TSymbolExpr(E.Operand).Name);
      if Sym = nil then
      begin
        ParseError(E.Coord, SErr_UndeclaredIdent);
        Exit;
      end
      else if not (Sym.NodeKind in [nkMethod, nkProperty, nkField]) then
      begin
        ParseError(E.Coord, SErr_IncompatibleTypes);
        Exit;
      end;
      Result :=
        CreateSymbolExpr(Sym.Name);
      TSymbolExpr(Result).reference := Sym;
      Result.Typ := FContext.FUntype;
      Result.Coord := E.Coord;
      Include(Result.Attr, eaInherited);
      SubstituteExpr(E,
        Result);
      Self.ReleaseExpr(E);
      CheckSymbol(TSymbolExpr(Result));
    end;
  end;

  procedure CheckInherited2(E: TBinaryExpr);

    function GetBaseSymbol(const s: TSymString): TSymbol;
    var
      parent: TSymbol;
    begin
      Result := nil;
      parent := FTopFunction.Parent;
      if parent.NodeKind <> nkType then
        Exit;
      case TType(parent).TypeCode of
        typClass: Result := TClassType(parent).FindBaseSymbol(S);
        typObject: Result := TObjectType(parent).FindBaseSymbol(S);
      end;
    end;

  var
    Sym: TSymbol;
  begin
    // Must be in a method or its nested function.
    // The method called must be owned by the base class.
    if (FTopFunction = nil) or (FTopFunction.NodeKind <> nkMethod) then
    begin
      ParseError(E.Coord, SErr_InheritedNotAllow);
      Exit;
    end;
    {Several formats:
       inherited; // ok A single inherited, which means to call the method of the same name of the base class.
       inherited docheck; // ok calls the specified method of the base class
       result := inherited docheck; // ok is placed in the expression
       result := inherited; // error inherited in the expression must take identifiers and parameters
       result := inherited prop // ok property or field
     }
    if (E.Left = nil) then
    begin
      Sym := GetBaseSymbol(FTopFunction.Name);
      if Sym = nil then
      begin
        if E.Parent <> nil then
          // inherited in the expression cannot omit the called method identifier
          ParseError(E.Coord, SErr_InheritedExpectId)
        else
        begin
          // If the base class does not have a method with the same name, and it is not in an expression, ignore this sentence.
          // Create an air conditioner  // Probably wrong translation, this is the original Chinese text: // 创建一个空调用
          E.Typ := FContext.FUntype;
          E.Left := CreateSymbolExpr(FContext.FNoopFunc.Name);
          TSymbolExpr(E.Left).reference := FContext.FNoopFunc;
          E.Left.Typ := FContext.FUntype;
          E.Left.Coord := E.Coord;
          E.Right := CreateListExpr;
          E.Right.Coord := E.Coord;
          E.Right.Typ := FContext.FUntype;
        end;
        Exit;
      end
      else if Sym.NodeKind <> nkMethod then
      begin
        ParseError(E.Coord, SErr_IncompatibleTypes);
        Exit;
      end;
      E.Left := CreateSymbolExpr(Sym.Name);
      TSymbolExpr(E.Left).reference := Sym;
      E.Left.Typ := FContext.FUntype;
      E.Left.Coord := E.Coord;
      E.Right := CreateListExpr;
      E.Right.Coord := E.Coord;
      // Construct parameters.
    end
    else
    begin
      Assert(E.Left.OpCode = opSYMBOL, 'CheckInherited: Expected left only symbol');
      Sym := GetBaseSymbol(TSymbolExpr(E.Left).Name);
      if Sym = nil then
      begin
        ParseError(E.Coord, SErr_UndeclaredIdent);
        Exit;
      end
      else if Sym.NodeKind <> nkMethod then
      begin
        ParseError(E.Coord, SErr_IncompatibleTypes);
        Exit;
      end;
      TSymbolExpr(E.Left).reference := Sym;
      E.Left.Typ := FContext.FUntype;
      if E.Right = nil then
        E.Right := CreateListExpr;
        //      CheckSymbol(E.Left);
    end;
    CheckCall(E);
  end;

  procedure CheckIntConst(E: TConstExpr);
  var
    I64: int64;
    I32: integer;
  begin
    Assert(E.Value.VT in [vtInt, vtInt64]);
    I64 := ValToInt64(E.Value);
    if (Int64Rec(I64).Hi = 0) and (I64 <= $7FFFFFFF) then
    begin
      I32 :=
        I64;
      if I32 >= 0 then
      begin
        if I32 < 128 then
          E.Typ := FContext.FShortIntType
        else if I32 < 256 then
          E.Typ := FContext.FByteType
        else if I32 < 32768 then
          E.Typ := FContext.FSmallIntType
        else if I32 < 65536 then
          E.Typ := FContext.FWordType
        else
          E.Typ := FContext.FLongIntType;
      end
      else
      begin
        if I32 >= -128 then
          E.Typ := FContext.FShortIntType
        else if I32 >= -32768 then
          E.Typ := FContext.FSmallIntType
        else
          E.Typ := FContext.FLongIntType;
      end;
    end
    else if I64 <= $FFFFFFFF then
      E.Typ := FContext.FLongWordType
    else if Int64Rec(I64).Hi and $80000000 = 0 then
      E.Typ := FContext.FInt64Type
    else
      E.Typ := FContext.FUInt64Type;
    Include(E.Attr, eaConst);
  end;

  procedure CheckConst(E: TConstExpr);
  begin
    case E.Value.VT of
      vtInt, vtInt64: CheckIntConst(E);
      vtReal: E.Typ := FContext.FRealType;
      vtCurr: E.Typ := FContext.FCurrencyType;
      vtStr, vtWStr: E.Typ := FContext.FStringType;
      vtAChr: E.Typ := FContext.FAnsiCharType;
      vtWChr: E.Typ := FContext.FWideCharType;
      vtBool: E.Typ := FContext.FBooleanType;
      vtPtr, vtSymbol, vtAddrOfSymbol, vtAddrOffset: E.Typ := FContext.FPointerType;
      vtSet: Assert(False, 'CheckConst:vtSet');
      //E.Typ := FContext.FEmptySetType;
      vtArray, vtRecord:
      // The composite type of array, record will not be evaluated here
      Assert(False, 'CheckConst:vtArray/vtRecord');
    end;
    Include(E.Attr, eaConst);
  end;

  function DoCheck(Expr: TExpr): TExpr; forward;

  procedure CheckList(un: TListExpr);
  var
    Temp: TExpr;
    I: integer;
  begin
    for I := 0 to un.Count - 1 do
    begin
      Temp := DoCheck(un.Items[I]);
      if Temp <> nil then
        un.Replace(I, Temp);
    end;
  end;

  function DoCheck(Expr: TExpr): TExpr;
  var
    un: TUnaryExpr;
    bin: TBinaryExpr;
    OldErr: integer;
  begin
    Result := Expr;
    if Expr = nil then
      Exit;
    // also check the ones that have been marked as invalid
    // For Expr, you can replace itself, but not its parent node
    OldErr := FErrorCount;
    un := nil;
    bin := nil;
    case OpKinds[Expr.OpCode] of
      opkUnary:
      begin
        un := TUnaryExpr(Expr);
        if un.OpCode <> opINHERITED then
          DoCheck(un.Operand);
      end;
      opkBinary:
      begin
        bin := TBinaryExpr(Expr);
        //if bin.OpCode <> opINHERITED then
        DoCheck(bin.Left);
        if bin.OpCode <> opMEMBER then
          DoCheck(bin.Right);
      end;
      opkList:
      begin
        CheckList(TListExpr(Expr));
        Expr.Typ := FContext.FUntype;
      end;
    end;
    if OldErr <> FErrorCount then
    begin
      Include(Expr.Attr, eaInvalid);
      Exit;
    end;
    case Expr.OpCode of
      opNE, opEQ, opLT, opLE, opGT, opGE: CheckRelOp(bin);
      opIN: CheckInOp(bin);
      opIS: CheckIsOp(bin);
      opAS: CheckAsOp(bin);
      opFDIV: CheckDivOp(bin);
      opIDIV, opMOD: CheckDivModOp(bin);
      opADD, opSUB, opMUL: CheckAddSubMulOp(bin);
      opOR, opXOR, opAND: CheckBitwiseOp(bin);
      opSHL, opSHR: CheckShiftOp(bin);
      opNOT: CheckNotOp(un);
      opNEG, opPOS: CheckNegOp(un);
      opCALL: Result := CheckCall(bin);
      opCAST: Result := CheckCast(bin);
      opMEMBER: Result := CheckSubSymbol(bin);
      opSYMBOL: Result := CheckSymbol(TSymbolExpr(Expr));
      opRANGE: CheckRange(bin);
      opINDEX: Result := CheckIndex(bin);
      opINHERITED: CheckInherited(un); //CheckInherited(bin);
      opSET: CheckSetOp(un);
      opLIST:
      begin
      end;
      opADDR: Result := CheckAddrOp(un);
      opDBLADDR: Result := CheckDblAddrOp(un);
      opINST: Result := CheckInst(un);
      opNIL:
      begin
        Expr.Typ := FContext.FPointerType;
        Include(Expr.Attr, eaConst);
      end;
      opCONST: CheckConst(TConstExpr(Expr));
      else
        Expr.Typ := FContext.FIntegerType;
        ParseError(Expr.Coord, 'Invalid opcode');
    end;
    if Expr <> Result then
      Expr := Result;
    Expr.Typ := Expr.Typ.OriginalType;
    if (eaConst in Expr.Attr) and not (Expr.OpCode in [opRANGE, opNIL, opCONST, opSYMBOL]) then
      Result := ConstantFold(Expr);
  end;

var
  OldErr: integer;
  E: TExpr;
begin
  OldErr := FErrorCount;
  E := DoCheck(Expr);
  if E <> nil then
    Expr := E;
  Result :=
    (OldErr = FErrorCount) and not (eaInvalid in Expr.Attr);
  if not Result then
    Include(Expr.Attr, eaInvalid);
  //  if FErrorCount > 0 then Expr.Typ := FContext.FAnytype;
end;

procedure TParser.CheckForward;

  procedure CheckForward_Func(Func: TFunction);
  begin
    if Func.StartStmt = nil then
      ParseError(Func.Coord, SErr_FuncNotImpl, [Func.Name]);
  end;

  procedure CheckForward_Method(typ: TType);
  var
    symbols: TSymbolTable;
    sym: TSymbol;
    i: integer;
  begin
    case typ.TypeCode of
      typClass: symbols := TClassType(typ).Symbols;
      typObject: symbols := TObjectType(typ).Symbols;
      typRecord: symbols := TRecordType(typ).Symbols;
      else
        Exit;
    end;
    for i := 0 to symbols.Count - 1 do
    begin
      sym := symbols[i];
      case sym.NodeKind of
        nkType: CheckForward_Method(TType(sym)); // Nested class, object, record.
        nkMethod: if TMethod(sym).StartStmt = nil then
            ParseError(sym.Coord, SErr_MethodNotImpl, [sym.Name]);
      end;
    end;
  end;

var
  i: integer;
  sym: TSymbol;
begin
  for i := 0 to FModule.Symbols.Count - 1 do
  begin
    sym := FModule.Symbols[i];
    case sym.NodeKind of
      nkFunc: CheckForward_Func(TFunction(sym));
      nkType: CheckForward_Method(TType(sym));
    end;
  end;
end;

procedure TParser.CheckFunction(F: TFunction);
begin
  func.CheckFunction(Self, F);
end;

function TParser.CheckOverloads(ExistsFunc, Func: TFunctionDecl): boolean;

  function CanOverload(f1, f2: TFunctionDecl): boolean;
  var
    i: integer;
  begin
    if f1.ParamCount <> f2.ParamCount then
      Result := True
    else
    begin
      for i := 0 to f1.ParamCount - 1 do
        if not f1.Params[i].ParamType.Equals(f2.Params[i].ParamType) then
        begin
          Result := True;
          Exit;
        end;
      Result := False;
    end;
  end;

begin
  while
    ExistsFunc <> nil do
  begin
    if not CanOverload(ExistsFunc, Func) then
    begin
      ParseError(Func.Coord, 'function declaration duplicated');
      Result := False;
      Exit;
    end;
    ExistsFunc :=
      ExistsFunc.NextOverload;
  end;
  Result := True;
end;

procedure TParser.ClearScopes;
begin
  FScopeList.Clear;
  //  while FScopeList.Count > 0 do
  //    LeaveScope;
end;

procedure TParser.ClearWithList;
begin
  while FWithList.Count > 0 do
    LeaveWithStmt;
end;

constructor TParser.Create(AContext: TCompileContext);
begin
  FScanner := TScanner.Create;
  FScanner.OnError := OnScannerError;
  FScanner.OnDirective := OnScannerDirective;
  FScanner.OnIfDefined := OnScannerIfDefined;
  FScanner.OnIfOpt := OnScannerIfOpt;
  FScanner.OnIfEval := OnScannerIfEval;
  //  FScanner.CodeSwitches := @FCodeSwitches;
  //  Include(FCodeSwitches, cdOverflowChecks);
  FContext := AContext;
  //  FSyntaxOptions := [synProcvarFpc];
  FAlignSize := 4;
  FPointerSize := SizeOf(Pointer);
  FMinEnumSize := 1;
  FHeader := TFunctionHeader.Create;
  FQId := TQualifiedId.Create;
  //FNodes := TList.Create;
  //FNodes.Capacity := 1024 * 64;
  //FTempExprList := TList.Create;
  //FTempExprList.Capacity := 100;
  //FExprList := TList.Create;
  //FExprList.Capacity := 1024 * 64;
  //FCurExprList := FExprList;
  FScopeList := TFPList.Create;
  FScopeList.Capacity := 16;
  FWithList := TFPList.Create;
  FWithList.Capacity := 16;
  FExternSymbols := TSymbolTable.Create(nil);
  FExternSymbols.Capacity := 1024 * 64;
  FDefinedSymbols := THashTable.Create(16);
  FMaxErrorCount := 10;
  FTokenIndex := -1;
  FTokenHead := -1;
end;

function TParser.CreateBinaryExpr(op: TExprOpCode; L: TExpr; R: TExpr): TBinaryExpr;
begin
  Result := FContext.GetCachedBinary;
  if not Assigned(Result) then
  begin
    Result := TBinaryExpr.Create;
    FModule.AddPrivate(Result);
  end;
  Result.Left := L;
  Result.Right := R;
  Result.OpCode := op;
  InitExpr(Result);
end;

function TParser.CreateConstExpr(typ: TExprOpCode): TConstExpr;
begin
  Result := FContext.GetCachedConst;
  if not Assigned(Result) then
  begin
    Result := TConstExpr.Create;
    FModule.AddPrivate(Result);
  end;
  Result.OpCode := typ;
  InitExpr(Result);
end;

function TParser.CreateElement(SymClass: TSymbolClass): TSymbol;
begin
  Result :=
    SymClass.Create;
  Result.Coord.Row := Scanner.CurRow;
  Result.Coord.Col := Scanner.CurColumn;
  Result.Coord.FileName := Scanner.CurFileName;
  if FInternalSection then
  begin
    Result.Attr := [saInternal];
    FModule.AddPrivate(Result);
  end
  else
    FContext.AddNode(Result);
end;

function TParser.CreateListExpr: TListExpr;
begin
  Result := FContext.GetCachedList;
  if not Assigned(Result) then
  begin
    Result := TListExpr.Create;
    FModule.AddPrivate(Result);
  end;
  Result.OpCode := opLIST;
  InitExpr(Result);
end;

function TParser.CreateStmt(Stmt: TStatementClass): TStatement;
begin
  Result := Stmt.Create;
  InitAstNode(Result);
  FModule.AddPrivate(Result);
end;

function TParser.CreateSymbolExpr(const Name: string): TSymbolExpr;
begin
  Result := FContext.GetCachedSymbol;
  if not Assigned(Result) then
  begin
    Result := TSymbolExpr.Create;
    FModule.AddPrivate(Result);
  end;
  Result.Name := Name;
  Result.OpCode := opSYMBOL;
  InitExpr(Result);
end;

function TParser.CreateType(TypClass: TTypeClass): TType;
begin
  Result := TType(CreateElement(TypClass));
  //  InitAstNode(Result);
end;

function TParser.CreateUnaryExpr(op: TExprOpCode; Operand: TExpr): TUnaryExpr;
begin
  Result := FContext.GetCachedUnary;
  if not Assigned(Result) then
  begin
    Result := TUnaryExpr.Create;
    FModule.AddPrivate(Result);
  end;
  Result.Operand := Operand;
  Result.OpCode := op;
  InitExpr(Result);
end;

function TParser.CurSymbols: TSymbolTable;
begin
  Result := TSymbolTable(FScopeList.Last);
end;

destructor TParser.Destroy;
begin
  //ClearNodes;
  ClearScopes;
  ClearWithList;
  FWithList.Free;
  FScopeList.Free;
  //FNodes.Free;
  //FTempExprList.Free;
  //FExprList.Free;
  FExternSymbols.Free;
  FDefinedSymbols.Free;
  FScanner.Free;
  ValClear(FTempValue);
  FHeader.Free;
  FQId.Free;
  inherited;
end;

procedure TParser.DoHint(const Coord: TAstNodeCoord; const Msg: string);
var
  Err: TParserErrorInfo;
begin
  if Assigned(FOnError) then
  begin
    Err := TParserErrorInfo.Create;
    Err.Row := Coord.Row;
    Err.Column := Coord.Col;
    Err.FileName := Coord.FileName;
    Err.ErrorMessage := Msg;
    Err.ErrorLevel := elHint;
    FOnError(Err);
    Err.Free;
  end;
end;

procedure TParser.DoHint(const Coord: TAstNodeCoord; const Msg: string; Args: array of const);
begin
  DoHint(Coord, Format(Msg, Args));
end;

procedure TParser.DoWarning(const Coord: TAstNodeCoord; const Msg: string);
var
  Err: TParserErrorInfo;
begin
  if Assigned(FOnError) then
  begin
    Err := TParserErrorInfo.Create;
    Err.Row := Coord.Row;
    Err.Column := Coord.Col;
    Err.FileName := Coord.FileName;
    Err.ErrorMessage := Msg;
    Err.ErrorLevel := elWarning;
    FOnError(Err);
    Err.Free;
  end;
end;

procedure TParser.DoWarning(const Coord: TAstNodeCoord; const Msg: string; Args: array of const);
begin
  DoWarning(Coord, Format(Msg, Args));
end;

procedure TParser.EnterScope(SymTable: TSymbolTable);
begin
  FScopeList.Add(SymTable);
end;

procedure TParser.EnterWithStmt(Sym: TSymbolExpr);
var
  Typ: TType;
begin
  Typ := Sym.Typ;
  if Typ.TypeCode = typPointer then
    Typ := TPointerType(Typ).RefType;
  Assert(Typ.TypeCode in [typClass, typInterface, typRecord, typObject]);
  Assert(Sym.reference <> nil);
  FWithList.Add(Sym);
end;

procedure TParser.Expect(T: TToken; Stop: boolean);

  function TokenText: string;
  begin
    case CurToken
      of
      tkIdentifier, tkStrConst, tkCharConst: Result := FCurTokenString;
      tkIntConst, tkHexConst, tkBinConst, tkOctalConst: Result := 'integer ' + IntToStr(fScanner.TokenValue.IntValue);
      tkFloatConst: Result := 'real ' + FloatToStr(FScanner.TokenValue.RealValue);
      else
        Result := TokenNames[CurToken];
    end;
  end;

  procedure Error;
  begin
    ParseError(Format('%s expected, but %s found', [TokenNames[T], TokenText]), Stop);
  end;

begin
  if CurToken <> T then
    Error;
end;

function TParser.FindSymbol(const S: string): TSymbol;
var
  I: integer;
begin
  for I := FScopeList.Count - 1 downto 0 do
  begin
    Result := TSymbolTable(FScopeList[I]).Find(S);
    if Result <> nil then
      Exit;
  end;
  Result := FExternSymbols.Find(S);
end;

{function TParser.FindSymbol(M: TModule; const S: string): TSymbol;
begin
  if M = nil then
    Result := FindSymbol(S)
  else if M = FModule then
    Result := FModule.FindSymbol(S)
  else
    Result := FExternSymbols.Find(M, S);
end;}

function TParser.FindSymbol(Typ: TType; const S: string): TSymbol;
begin
  case Typ.TypeCode of
    typClass: Result := TClassType(typ).FindSymbol(S);
    typRecord: Result := TRecordType(typ).FindSymbol(S);
    typInterface: Result := TInterfaceType(typ).FindSymbol(S);
    typObject: Result := TObjectType(typ).FindSymbol(S);
    else
      Result := nil;
  end;
end;

function TParser.FindWith(const S: string; out Sym: TSymbolExpr; out Elem: TSymbol): boolean;
var
  I: integer;
  Typ: TType;
begin
  Result := True;
  for I := FWithList.Count - 1 downto 0 do
  begin
    Sym := TSymbolExpr(FWithList[I]);
    Typ := Sym.Typ;
    if Typ.TypeCode = typPointer then
      Typ := TPointerType(Typ).RefType;
    Elem := FindSymbol(Typ, S);
    if Elem <> nil then
      Exit;
  end;
  Elem := nil;
  Sym := nil;
  Result := False;
end;

function TParser.GetOpenArrayType(const typ: TType): TOpenArrayType;
begin
  if saInternal in typ.Attr then
  begin
    Result := TOpenArrayType(CreateType(TOpenArrayType));
    TOpenArrayType(Result).ElementType :=
      typ;
  end
  else
    Result := FContext.GetOpenArrayType(typ);
end;

procedure TParser.GetOverloadBegin(Func: TFunctionDecl);
begin
  FCurOverloadFunc := Func;
end;

procedure TParser.GetOverloadEnd;
begin
  FCurOverloadFunc := nil;
  FCurSymbolPos := nil;
end;

function TParser.GetOverloadNext: TFunctionDecl;

  function NextMeth_Class(T: TClassType): TFunctionDecl;
  var
    Sym: TSymbol;
  begin
    Result := nil;
    if T = nil then
      Exit;
    // todo 1: You may need to consider a class that implements the interface
    repeat
      Sym := T.FindCurSymbol(FCurOverloadFunc.Name);
      if Sym.NodeKind = nkMethod then
        Result := TMethod(sym);
      T := T.Base;
    until (T = nil) or (Result <> nil);
  end;

  function NextMeth_Object(T: TObjectType): TFunctionDecl;
  var
    Sym: TSymbol;
  begin
    Result := nil;
    if T = nil then
      Exit;
    repeat
      Sym := T.FindCurSymbol(FCurOverloadFunc.Name);
      if Sym.NodeKind = nkMethod then
        Result := TMethod(sym);
      T := T.Base;
    until (T = nil) or (Result <> nil);
  end;

  function NextMeth_Intf(T: TInterfaceType): TFunctionDecl;
  var
    Sym: TSymbol;
  begin
    Result := nil;
    if T = nil then
      Exit;
    repeat
      Sym := T.FindCurSymbol(FCurOverloadFunc.Name);
      if Sym.NodeKind = nkMethod then
        Result := TMethod(sym);
      T := T.Base;
    until (T = nil) or (Result <> nil);
  end;

  function NextOverloadMeth: TFunctionDecl;
  var
    T: TSymbol;
  begin
    Result := nil;
    T := FCurOverloadFunc.Parent;
    Assert(T.NodeKind = nkType, 'NextOverloadMeth: T is not type');
    case TType(T).TypeCode of
      typRecord: Exit;
      typClass: Result := NextMeth_Class(TClassType(T).Base);
      typObject: Result := NextMeth_Object(TObjectType(T).Base);
      typInterface: Result := NextMeth_Intf(TInterfaceType(T).Base);
      else
        Assert(False, 'NextOverloadMeth: T is not class/object/interface');
    end;
  end;

  function NextOverloadExternal: TFunctionDecl;
  var
    Sym: TSymbol;
  begin
    // Take external symbols
    if FCurSymbolPos = nil then
    begin
      FCurSymbolPos := FExternSymbols.GetStart(FCurOverloadFunc.Name);
      // Skip first
      FExternSymbols.GetNext(FCurSymbolPos);
    end;
    repeat
      Sym := FExternSymbols.GetNext(FCurSymbolPos);
      if (Sym <> nil) and (Sym.NodeKind in [nkFunc, nkExternalFunc]) then
      begin
        Result := TFunctionDecl(Sym);
        Exit;
      end;
    until Sym = nil;
    Result := nil;
  end;

  function NextOverload: TFunctionDecl;
  var
    P, Sym: TSymbol;
  begin
    //    if FCurOverloadFunc.Parent.NodeKind = nkModule then
    if (FCurOverloadFunc.Module <> Self.FModule) then
    begin
      Result := NextOverloadExternal;
      Exit;
    end;
    P := FCurOverloadFunc.Parent;
    if P.NodeKind <> nkModule then
    begin
      if P.NodeKind in [nkFunc, nkMethod] then
        P := P.Parent;
      // Allow nested function overloading
      while P.NodeKind in [nkFunc, nkMethod] do
      begin
        Sym := TFunction(P).LocalSymbols.Find(FCurOverloadFunc.Name);
        if Sym.NodeKind in [nkFunc, nkExternalFunc, nkMethod] then
        begin
          Result := TFunctionDecl(Sym);
          Exit;
        end;
        P := P.Parent;
      end;
      // Take the module
      while P.NodeKind <> nkModule do
      begin
        P := P.Parent;
        Assert(P <> nil, 'NextOverload: P <> nil');
      end;
      Sym := TModule(P).Symbols.Find(FCurOverloadFunc.Name);
      if (Sym <> nil) and (Sym.NodeKind in [nkFunc, nkExternalFunc, nkMethod]) then
      begin
        Result := TFunctionDecl(Sym);
        Exit;
      end;
    end;
    // Take external symbols
    if FCurSymbolPos = nil then
      FCurSymbolPos :=
        FExternSymbols.GetStart(FCurOverloadFunc.Name);
    Result := NextOverloadExternal;
  end;

begin
  if FCurOverloadFunc.NodeKind = nkMethod then
    FCurOverloadFunc := NextOverloadMeth
  else
    FCurOverloadFunc := NextOverload;
  Result := FCurOverloadFunc;
end;

function TParser.GetSetType(typ: TSubrangeType): TSetType;
begin
  if typ.SetType = nil then
  begin
    typ.SetType := TSetType.Create;
    typ.SetType.Name := '$' + typ.Name + '_Set';
    typ.SetType.RangeType := typ;
    typ.SetType.Update;
    typ.SetType.Coord := typ.Coord;
    if saInternal in typ.Attr then
      Include(typ.SetType.Attr, saInternal);
    if Self.FInternalSection then
      FModule.AddPrivate(typ.SetType)
    else
      FContext.AddNode(typ.SetType);
    typ.Parent.Add(typ.SetType);
  end;
  Result := typ.SetType;
end;

function TParser.GetSetType(typ: TEnumType): TSetType;
begin
  // todo 1: Take into account that this Subrange range exceeds 0..255
  Result := GetSetType(GetSubrangeType(typ));
end;

function TParser.GetSubrangeType(typ: TEnumType): TSubrangeType;
begin
  if typ.SubrangeType = nil then
  begin
    typ.SubrangeType := TSubrangeType.Create;
    typ.SubrangeType.Name := '$' + typ.Name + '_Rng';
    typ.SubrangeType.BaseType := typ;
    typ.SubrangeType.Coord := typ.Coord;
    if saInternal in typ.Attr then
      Include(typ.SubrangeType.Attr, saInternal);
    if Self.FInternalSection then
      FModule.AddPrivate(typ.SubrangeType)
    else
      FContext.AddNode(typ.SubrangeType);
    typ.Parent.Add(typ.SubrangeType);
  end;
  typ.SubrangeType.
    RangeBegin := typ.LowValue;
  typ.SubrangeType.RangeEnd := typ.HighValue;
  Result := typ.SubrangeType;
end;

procedure TParser.InitAstNode(ANode: TAstNode);
begin
  with FTokenBuffer[FTokenIndex].Coord do
  begin
    ANode.Coord.Row := Row;
    ANode.Coord.Col := Col;
    ANode.Coord.FileName :=
      FileName;
  end;
end;

procedure TParser.InitExpr(Expr: TExpr);
begin
  with FTokenBuffer[FTokenIndex].Coord do
  begin
    Expr.Coord.Row := Row;
    Expr.Coord.Col := Col;
    Expr.Coord.FileName := FileName;
  end;
  Expr.Switches := FCodeSwitches;
end;

procedure TParser.InternalError(const Msg: string);
begin
  Self.ParseError(SErr_InternalError, [Msg], True);
end;

function TParser.IsConstantOutOfRange(typ: TType; Value: int64; Strict: boolean): boolean;
var
  sub: TSubRangeType;
  r1, r2: int64;
begin
  Result := True;
  case typ.TypeCode of
    typInt, typBool, typChar:
    begin
      sub := FContext.GetSubrangeType(typ);
      r1 := sub.RangeBegin;
      r2 := sub.RangeEnd;
    end;
    typEnum: if Strict then
      begin
        r1 := TEnumType(typ).LowValue;
        r2 := TEnumType(typ).HighValue;
      end
      else
      begin
        if typ.Size = 1 then
          sub := FContext.FShortintRangeType
        else if typ.Size = 2 then
          sub := FContext.FSmallintRangeType
        else
          sub := FContext.FLongintRangeType;
        r1 := sub.RangeBegin;
        r2 := sub.RangeEnd;
      end;
    typSubrange: if Strict then
      begin
        r1 := TSubrangeType(typ).RangeBegin;
        r2 := TSubrangeType(typ).RangeEnd;
      end
      else
      begin
        if typ.Size = 1 then
          sub := FContext.FShortintRangeType
        else if typ.Size = 2 then
          sub := FContext.FSmallintRangeType
        else if typ.Size = 8 then
          sub := FContext.FInt64RangeType
        else
          sub := FContext.FLongintRangeType;
        r1 := sub.RangeBegin;
        r2 := sub.RangeEnd;
      end
    else
      Result := False;
  end;
  if Result then
    Result := (Value < r1) or (Value > r2);
end;

function TParser.IsConstantOutOfRange(typ: TType; const Value: TValueRec; Strict: boolean): boolean;
begin
  Result := IsConstantOutOfRange(typ, ValToInt64(Value), Strict);
end;

function TParser.IsSameArgs(L1, L2: TFuncParamList): boolean;

  function IsSameArg(A1, A2: TFuncParam): boolean;
  begin
    Result := (A1.ParamType = A2.ParamType) and (A1.Modifier = A2.Modifier) and (A1.ArgKind = A2.ArgKind);
  end;

var
  I, C1, C2: integer;
begin
  Result := False;
  if L1 <> nil then
    C1 := L1.Count
  else
    C1 := 0;
  if L2 <> nil then
    C2 := L2.Count
  else
    C2 := 0;
  if C1 <> C2 then
    Exit;
  for I := 0 to C1 - 1 do
    if not IsSameArg(TFuncParam(L1[I]), TFuncParam(L2[I])) then
      Exit;
  Result := True;
end;

function TParser.IsVisible(Ref, Referred: TSymbol): boolean;

  function PrivCanAccess(Ref: TSymbol; Referred: TType): boolean;
  begin
    // Determine whether Ref can access the private members of Referred
    // As long as Ref is a member of Referred or a member of nested type
    // Or Ref and Referred are the same unit
    while
      Ref.Parent <> nil do
    begin
      if Ref = Referred then
      begin
        Result := True;
        Exit;
      end;
      Ref := Ref.Parent;
    end;
    Result := (Ref.NodeKind = nkModule) and (Ref = Referred.Module);
  end;

  function IsInhFrom(Ref: TSymbol; Referred: TType): boolean;
  begin
    Result := False;
    if (Ref.NodeKind = nkType) and (TType(Ref).TypeCode = Referred.TypeCode) then
      case Referred.TypeCode of
        typClass: Result := TClassType(Ref).IsInheritedFrom(TClassType(Referred));
        typObject:
          Result := TObjectType(Ref).IsInheritedFrom(TObjectType(Referred));
      end;
  end;

  function ProtCanAccess(Ref: TSymbol; Referred: TType): boolean;
  begin
    Result := PrivCanAccess(Ref, Referred) or IsInhFrom(Ref, Referred);
  end;

  function StrictPrivCanAccess(Ref: TSymbol; Referred: TType): boolean;
  begin
    while Ref.Parent <> nil do
    begin
      if Ref = Referred then
      begin
        Result := True;
        Exit;
      end;
      Ref := Ref.Parent;
    end;
    Result := False;
  end;

  function StrictProtCanAccess(Ref: TSymbol; Referred: TType): boolean;
  begin
    Result := StrictPrivCanAccess(Ref, Referred) or IsInhFrom(Ref, Referred);
  end;

  function PubCanAccess(Ref: TSymbol; Referred: TType): boolean;
  var
    Vis: TMemberVisibility;
    S: TSymbol;
  const
    VisN: array[TMemberVisibility] of
      byte = (4, 0, 1, 2, 4, 4, 4, 4);
  begin
    Vis := visPublic;
    while Referred <> nil do
    begin
      if VisN[Referred.Visibility] < VisN[Vis] then
        Vis := Referred.Visibility;
      S := Referred.Parent;
      if Assigned(S) and (s.NodeKind = nkType) then
        Referred := TType(S)
      else
        Break;
    end;
    case Vis of
      visPrivate: Result := PrivCanAccess(Ref, Referred);
      visProtected: Result := ProtCanAccess(Ref, Referred);
      visStrictPrivate: Result := StrictPrivCanAccess(Ref, Referred);
      visStrictProtected: Result := StrictProtCanAccess(Ref, Referred);
      else
        Result := True;
    end;
  end;

var
  S: TSymbol;
begin
  Result := True;
  S := Referred.Parent;
  if S = nil then
    Exit;
  {
  visDefault,
  visPrivate,         [Owner, NestOfOwner, Module]
  visProtected,       [Owner, NestOfOwner, Module, SubOfOwner]
  visPublic,          [Owner, NestOfOwner, Module, SubOfOwner, Outter]
  visPublished,       [Owner, NestOfOwner, Module, SubOfOwner, Outter]
  visAutomated,       [Owner, NestOfOwner, Module, SubOfOwner, Outter]
  visStrictPrivate,   [Owner, NestOfOwner]
  visStrictProtected  [Owner, NestOfOwner, SubOfOwner]
  }
  case S.NodeKind of
    nkType: if TType(S).TypeCode in [typClass, typObject, typRecord] then
      begin
        case Referred.Visibility
          of
          visPrivate: Result := PrivCanAccess(Ref, TType(S));
          visProtected: Result := ProtCanAccess(Ref, TType(S));
          visPublic, visPublished, visAutomated: Result := PubCanAccess(Ref, TType(S));
          visStrictPrivate: Result := StrictPrivCanAccess(Ref, TType(S));
          visStrictProtected: Result := StrictProtCanAccess(Ref, TType(S));
          else
            Result := True;
        end;
      end
      else if TType(S).TypeCode = typInterface then
        Result := True  // Symbols at the Module level can be used
      else
        ParseError(SErr_InternalError, ['Referred.Parent invalid']);
    nkModule, nkFunc, nkMethod: Result := True;
    else
      ParseError(SErr_InternalError, ['Referred.Parent invalid']);
  end;
end;

procedure TParser.LeaveScope;
begin
  if FScopeList.Count > 0 then
  begin
    FScopeList.Delete(FScopeList.Count - 1);
  end;
end;

procedure TParser.LeaveWithStmt;
begin
  if FWithList.Count > 0 then
  begin
    FWithList.Delete(FWithList.Count - 1);
  end;
end;

procedure TParser.NextToken;
const
  WhitespaceTokensToIgnore = [tkWhitespace, tkIllegalChar, tkComment, tkLineEnding];
begin
  if FTokenIndex <> FTokenHead then
  begin
    Inc(FTokenIndex);
    if FTokenIndex > MAX_UNGET then
      FTokenIndex := 0;
  end
  else
  begin
    Inc(FTokenIndex);
    if FTokenIndex > MAX_UNGET then
      FTokenIndex := 0;
    FTokenHead := FTokenIndex;
    FTokenBuffer[FTokenIndex].Token := FScanner.FetchToken;
    Assert(not (FTokenBuffer[FTokenIndex].Token in WhitespaceTokensToIgnore));
    FTokenBuffer[FTokenIndex].TokenStr := Scanner.CurTokenString;
    with FTokenBuffer[FTokenIndex].Coord do
    begin
      FileName := Scanner.CurFileName;
      Col := Scanner.CurColumn;
      Row := Scanner.CurRow;
    end;
  end;
  with FTokenBuffer[FTokenIndex] do
  begin
    FCurTokenString := TokenStr;
    FCurToken := Token;
  end;
end;

procedure TParser.OnScannerDirective(var dinfo: TDirectiveInfo);
begin
  case dinfo.Directive of
    cdBoolEval..cdSafeDivide: if dinfo.State then
        Include(FCodeSwitches, dinfo.Directive)
      else
        Exclude(FCodeSwitches, dinfo.Directive);
    cdTypeInfo: Self.FRttiInfo := dinfo.State;
    cdTypedAddress: Self.FTypedAddress := dinfo.State;
    cdWriteableConst: Self.FWriteableConst := dinfo.State;
    cdAlign: if dinfo.ArgInt1 > 0 then
        Self.FAlignSize := dinfo.ArgInt1
      else if dinfo.State then
        Self.FAlignSize := 4
      else
        Self.FAlignSize := 1;
    cdMinEnumSize: if dinfo.ArgInt1 > 0 then
        Self.FMinEnumSize := dinfo.ArgInt1
      else if dinfo.State then
        Self.FMinEnumSize := 4
      else
        Self.FMinEnumSize := 1;
    cdDefine: FDefinedSymbols.Add(dinfo.ArgStr1, nil);
    cdUndef: FDefinedSymbols.Remove(dinfo.ArgStr1);
    cdMode: if SameText(dinfo.ArgStr1, 'objfpc') then
      begin
        Include(FSyntaxOptions, synProcvarFpc);
      end
      else if SameText(dinfo.ArgStr1, 'delphi') or SameText(dinfo.ArgStr1, 'delphiunicode') then
      begin
        Exclude(FSyntaxOptions, synProcvarFpc);
      end;
  end;
end;

procedure TParser.OnScannerError(const Msg: string; Stop: boolean);
begin
  ParseError(Msg, Stop);
end;

procedure TParser.OnScannerIfDefined(const S: string; out IsDefined: boolean);
begin
  IsDefined := FDefinedSymbols.IsExists(S);
end;

procedure TParser.OnScannerIfEval(out IsDefined: boolean);
var
  E: TExpr;
  V: TValueRec;
  I: integer;
  FBakTokens: array[0..MAX_UNGET] of TTokenInfo;
  FBakIndex, FBakHead: smallint;
begin
  // Save
  for I := 0 to High(FBakTokens) do
    FBakTokens[I] := FTokenBuffer[I];
  FBakIndex := FTokenIndex;
  FBakHead := FTokenHead;
  Finalize(FTokenBuffer, Length(FTokenBuffer));
  for
    I := 0 to Length(FTokenBuffer) - 1 do
    FTokenBuffer[I].Token := tkEOF;
  FTokenIndex := -1;
  FTokenHead := -1;
  NextToken;
  E := ParseConstExpr;
  try
    ValInit(V);
    IsDefined := CheckConstExpr(E) and TryEvalGet(E, V);
    if IsDefined then
      case V.VT of
        vtInt: IsDefined := V.VInt <> 0;
        vtInt64: IsDefined := V.VInt64 <> 0;
        vtBool: IsDefined := V.VBool <> 0;
        else
          IsDefined := False;
          ParseError(E.Coord, SErr_ExpectConstExpr, True);
      end;
  except
    IsDefined := False;
  end;
  ValClear(V);
  ReleaseExpr(E);
  // Restore
  for I := 0 to High(FBakTokens) do
    FTokenBuffer[I] := FBakTokens[I];
  FTokenIndex := FBakIndex;
  FTokenHead := FBakHead;
end;

procedure TParser.OnScannerIfOpt(C: char; out IsSet: boolean);
begin
  case C of
    'A', 'a': IsSet := Self.FAlignSize > 1;
    'Q', 'q': IsSet := cdOverflowChecks in FCodeSwitches;
    'R', 'r': IsSet := cdRangeChecks in FCodeSwitches;
    'B', 'b': IsSet := cdBoolEval in FCodeSwitches;
    'I', 'i': IsSet := cdIOChecks in FCodeSwitches;
    'U', 'u': IsSet := cdSafeDivide in FCodeSwitches;
    'M', 'm': IsSet := Self.FRttiInfo;
    'T', 't': IsSet := Self.FTypedAddress;
    'J', 'j': IsSet := Self.FWriteableConst;
    else
      isSet := False;
  end;
end;

procedure TParser.OpenCode(const S: string);
begin
  Scanner.Open(S);
end;

procedure TParser.OpenFile(const FileName: string);
begin
  Scanner.OpenFile(FileName);
end;

function TParser.Parse: TModule;
begin
  NextToken;
  case CurToken of
    tkProgram: Result := ParseProgram;
    tkUnit: Result := ParseUnit;
    else
      ParseError('unit, program expected', True);
      Result := nil;
  end;
end;

function TParser.ParseAddExpr: TExpr;

  function AddOp(T: TToken): TExprOpCode;
  begin
    case T of
      tkPlus: Result := opAdd;
      tkMinus: Result := opSUB;
      tkOr: Result := opOR;
      tkXor: Result := opXOR;
      else
        Result := opNone;
//      tkPower                 : Result := opPower;
//      tkSymmetricalDifference : Result := opSymmetricalDifference;
    end;
  end;

var
  left, right: TExpr;
  op: TExprOpCode;
begin
  {
  <AddExpr>		::= <MulExpr>
  			  | <AddExpr> <AddOp> <MulExpr>
  }
  Result := ParseMulExpr;
  op :=
    AddOp(CurToken);
  while op <> opNONE do
  begin
    NextToken;
    left := Result;
    right := ParseMulExpr;
    Result := CreateBinaryExpr(op, left, right);
    op := AddOp(CurToken);
  end;
end;

procedure TParser.ParseBlock(Parent: TSymbol);

  function ParseEntryCode(const AName: string): TFunction;
  var
    StateInfo: TParseStateInfo;
  begin
    Result := TFunction(CreateElement(TFunction));
    Exclude(Result.Attr, saInternal);
    Result.Name := AName;
    Result.Parent := FModule;
    FCurFunction := Result;
    StateSet(psInFunc, StateInfo);
    Result.StartStmt := ParseCompoundStmt;
    StateRestore(StateInfo);
    FCurFunction := nil;
  end;

begin
  {
  <Block>			::= <OptDeclSection> <OptExportBlock> <CompoundStmt> <OptExportBlock>
  }
  while True do
  begin
    case CurToken of
      tkType: Self.ParseTypeSection(Parent);
      tkVar, tkThreadVar: Self.ParseVarSection(Parent);
      tkConst: Self.ParseConstSection(Parent);
      tkResourceString: Self.ParseResStringSection(Parent);
      tkProcedure, tkFunction, tkConstructor, tkDestructor: Self.ParseFunction(Parent);
      tkClass:
      begin
        NextToken;
        if CurToken in [tkProcedure, tkFunction] then
        begin
          Include(Self.FCurStates, psInClassPrefix);
          Self.ParseFunction(FModule);
        end
        else
          ParseError(SErr_ExpectProcOrFunc, True);
      end;
      tkLabel: Self.ParseLabelSection(Parent);
      else
        Expect(tkBegin);
        FModule.InitializeFunc := ParseEntryCode('$main');
        Expect(tkDot);
        Break;
    end;
  end;
end;

function TParser.ParseCaseStmt: TCaseStmt;

  procedure IncompatibleErr(const Coord: TAstNodeCoord; t1, t2: TTypeCode);
  begin
    ParseError(Coord, SErr_IncompatibleTypes2, [TypeNames[t1], TypeNames[t2]]);
  end;
  {
   function CheckCaseList(List: TListExpr; Typ: TType): Boolean;
     function CheckCaseExpr(E: TExpr; ExpectTyp: TType): Boolean;
     var
       T2: TType;
     begin
       Result := CheckConstExpr(E);
       if not Result then Exit;
       T2 := E.Typ.NormalType;
       if not CheckAssignCompatibility(ExpectTyp, T2) then
       begin
         Result := False;
         IncompatibleErr(E.Coord, ExpectTyp.TypeCode, T2.TypeCode);
       end;
     end;
   var
     E: TExpr;
     I: Integer;
   begin
     for I := 0 to List.Count - 1 do
     begin
       E := List.Items[I];
       if E.OpCode = opRANGE then
       begin
         Result := CheckCaseExpr(TBinaryExpr(E).Left, Typ)
             and CheckCaseExpr(TBinaryExpr(E).Right, Typ);
       end
       else
       begin
         Result := CheckCaseExpr(E, Typ);
       end;
       if not Result then Exit;
     end;
     Result := True;
   end;
  }
  function CheckCaseExpr(E: TExpr; ExpectTyp: TType): boolean;
  var
    T2: TType;
  begin
    Result := CheckConstExpr(E);
    if not Result then
      Exit;
    T2 := E.Typ.NormalType;
    if not CheckAssignCompatibility(ExpectTyp, T2) then
    begin
      Result := False;
      IncompatibleErr(E.Coord, ExpectTyp.TypeCode,
        T2.TypeCode);
    end;
  end;

  procedure AddRanges(Selector: TCaseSelector; Stmt: TCaseStmt; List: TListExpr);
  var
    E: TExpr;
    Typ: TType;
    Start, Stop: int64;
    I: integer;
  begin
    Start := 0;
    Stop :=
      0;
    Typ := Stmt.Expr.Typ;
    for I := 0 to List.Count - 1 do
    begin
      E := List.Items[I];
      ValClear(
        FTempValue);
      if E.OpCode = opRANGE then
      begin
        if not CheckCaseExpr(TBinaryExpr(E).Left, Typ) then
          Continue;
        if not CheckCaseExpr(TBinaryExpr(E).Right, Typ) then
          Continue;
        if not TryEvalGet(TBinaryExpr(E).Left, FTempValue) then
          Continue;
        Start := ValToInt64(FTempValue);
        ValClear(FTempValue);
        if not TryEvalGet(TBinaryExpr(E).Right, FTempValue) then
          Continue;
        Stop := ValToInt64(FTempValue);
        if IsConstantOutOfRange(Typ, Start) or IsConstantOutOfRange(Typ, Stop) then
        begin
          ParseError(E.Coord, SErr_ConstantOutOfRange);
          Continue;
        end;
      end
      else
      begin
        if not CheckCaseExpr(E, Typ) then
          Continue;
        if not TryEvalGet(E, FTempValue) then
          Continue;
        Start := ValToInt64(FTempValue);
        Stop := Start;
        if IsConstantOutOfRange(Typ, Start) then
        begin
          ParseError(E.Coord, SErr_ConstantOutOfRange);
          Continue;
        end;
      end;
      if not Stmt.Contains(Start, Stop) and not Selector.Contains(Start, Stop) then
      begin
        Selector.AddRange(Start, Stop);
        with Selector do
          Values[Count - 1].Coord := E.Coord;
      end
      else
        ParseError(E.Coord, SErr_CaseLabelDuplicated);
    end;
  end;

var
  E: TListExpr;
  Selector: TCaseSelector;
begin
  Result := TCaseStmt(CreateStmt(TCaseStmt));
  NextToken;
  Result.Expr := ParseExpr;
  if CheckExpr(Result.Expr) then
  begin
    if not Result.Expr.Typ.IsOrdinal then
      ParseError(Result.Expr.Coord, SErr_OrdinalRequired);
    if Result.Expr.IsTypeSymbol then
      ParseError(Result.Expr.Coord, SErr_VarRequired);
  end;
  Expect(tkOf);
  NextToken;
  while True do
  begin
    case CurToken of
      tkElse:
      begin
        NextToken;
        Result.Default := Self.ParseStmtList(Result, [tkEnd]);
      end;
      tkEnd: Break;
      else
        E := ParseSetElementList as TListExpr;
        // CheckCaseList(E, Result.Expr.Typ);
        Expect(tkColon);
        NextToken;
        // parse stmt;
        Selector := TCaseSelector.Create;
        Result.AddSelector(Selector);
        AddRanges(Selector, Result, E);
        ReleaseExpr(E);
        Selector.Stmt := ParseStatement(Result);
//      Expect(tkSemicolon);
        if CurToken = tkSemicolon then
          NextToken;
    end;
  end;
  Expect(tkEnd);
  NextToken;
  // todo 1: Check if the case value is repeated
end;

function TParser.ParseClassRefType: TClassRefType;
var
  Typ: TType;
  Sym: TSymbol;
begin
  NextToken;  // skip 'of'
  sym := ParseQualifiedSym;
  if Sym = nil then
  begin
    if FQId.CountOfNames = 1 then
    begin
      Typ := TUnresolvedType.Create;  // Do not use CreateElement, because this TUnresolvedType will be released
      Typ.Name := FQID.Name;
    end
    else
    begin
      ParseError(SErr_UndeclaredIdent, [FQId.Id]);
      Typ := FContext.FTObjectType;
    end;
  end
  else if Sym.NodeKind <> nkType then
  begin
    ParseError(SErr_SymbolNotType, [FQId.Id]);
    Typ := FContext.FTObjectType;
  end
  else
    Typ := TType(Sym);
  FQID.Reset;
  {if Typ.TypeCode = typClass then
    Result := TClassType(Typ).GetClassRef
  else begin
    parseError(SErr_ClassRequired);
    Result := FContext.FTObjectType.GetClassRef
  end;}
  Result := TClassRefType(CreateType(TClassRefType));
  if Typ.TypeCode = typClass then
    Result.RefType := TClassType(Typ)
  else
  begin
    Result.RefType := FContext.FTObjectType;
    parseError(SErr_ClassRequired);
  end;
end;

function TParser.ParseClassType(const TypName: string; Parent: TSymbol; out NotAddSym: boolean): TClassType;

  procedure ParseBaseClass(ClassTyp: TClassType);
  var
    Typ: TSymbol;
  begin
    NextToken; // skip '('
    Typ := ParseQualifiedSym;
    if Typ.NodeKind = nkType then
      Typ := TType(Typ).OriginalType;
    if (Typ.NodeKind <> nkType) or (TType(Typ).TypeCode <> typClass) then
      ParseError(SErr_InvalidBaseClass)
    else
      Result.Base :=
        TClassType(Typ);
    if saForward in Result.Base.Attr then
      ParseError(Result.Coord, SErr_ClassNotComplete, [Result.Base.Name]);
    while CurToken = tkComma do
    begin
      // Analyze interface list
      NextToken;
      Typ := ParseQualifiedSym;
      if (Typ.NodeKind <> nkType) or (TType(Typ).TypeCode <> typInterface) then
        ParseError(SErr_ExpectIntfType)
      else
        ClassTyp.AddInterface(TInterfaceType(Typ));
    end;
    Expect(tkBraceClose);
    NextToken;
  end;

  function FindForwardClass(const S: string): TClassType;
  var
    E: TSymbol;
  begin
    E := CurSymbols.Find(S);
    if Assigned(E) and (E.ClassType = TClassType) and (saForward in E.Attr) then
      Result := TClassType(E)
    else
      Result := nil;
  end;

  function IsSameMethodDecl(F1, F2: TMethod): boolean;
  begin
    Result := (F1.ReturnType = F2.ReturnType) and IsSameArgs(F1.Params, F2.Params) and
      (F1.CallConvention = F2.CallConvention) and (F1.MethodKind = F2.MethodKind);
  end;

type
  TOverrideCheckFlag = (cfOk, cfNotVirtual, cfDiffers, cfCannotAccess);

  function CanAccess(Cur: TClassType; S: TSymbol): boolean;
  begin
    Result := not (S.Visibility in [visPrivate, visStrictPrivate]) or
      ((S.Visibility = visStrictPrivate) and (Cur = S.Parent)) or ((S.Visibility = visPrivate) and
      (Cur.Module = S.Module));
  end;

  function IsOverrided(typ: TClassType; Meth, BaseMeth: TMethod): TOverrideCheckFlag;
  begin
    if not ((fmVirtual in BaseMeth.Modifiers) or (fmDynamic in BaseMeth.Modifiers)) and
      (fmStatic in Meth.Modifiers) then
      Result := cfNotVirtual
    else if IsSameMethodDecl(BaseMeth, Meth) then
    begin
      if CanAccess(typ, BaseMeth) then
        Result := cfOk
      else
        Result := cfCannotAccess;
    end
    else
      Result := cfDiffers;
  end;

  procedure CheckOverrides(typ: TClassType; Meth: TMethod);
  var
    Sym: TSymbol;
    BaseMeth: TMethod;
    Ok, Ok2: TOverrideCheckFlag;
  begin
    Sym := typ.FindBaseSymbol(Meth.Name);
    if (Sym = nil) or (Sym.NodeKind <> nkMethod) then
    begin
      ParseError(Meth.Coord, SErr_NoVirtualMethod, [Meth.Name]);
      Exit;
    end;
// repeat
    BaseMeth := TMethod(Sym);
    Ok2 := cfOk;
    repeat
      Ok := IsOverrided(typ, Meth, BaseMeth);
      if Ok = cfOk then
      begin
        Meth.VTIndex := BaseMeth.VTIndex;
        if fmDynamic in BaseMeth.Modifiers then
          Include(Meth.Modifiers, fmDynamic);
        if fmVirtual in BaseMeth.Modifiers then
          Include(Meth.Modifiers, fmVirtual);
        Break;
      end;
      if Ok2 <> cfCannotAccess then
        Ok2 := Ok;
      BaseMeth := TMethod(BaseMeth.NextOverload);
    until BaseMeth = nil;
    if (Ok <> cfOk) then
    begin
      case Ok2 of
        cfNotVirtual, cfCannotAccess: ParseError(Meth.Coord, SErr_SymbolNotAccess, [Meth.Name]);
        cfDiffers: ParseError(Meth.Coord, SErr_OverridedDiffers, [Meth.Name]);
      end;
    end;
//  Meth := TMethod(Meth.NextOverload);
//until Meth = nil;
  end;

  function IsImplemented(typ: TClassType; IntfMeth, ImplMeth: TMethod): TOverrideCheckFlag;
  begin
    if IsSameMethodDecl(ImplMeth, IntfMeth) then
    begin
      if CanAccess(typ, ImplMeth) then
        Result := cfOk
      else
        Result := cfCannotAccess;
    end
    else
      Result := cfDiffers;
  end;

  procedure CheckImplMethods(typ: TClassType; IntfEntry: TClassIntfEntry; MethIndex: integer; IntfMeth: TMethod);
  var
    Sym: TSymbol;
    ImplMeth: TMethod;
    Ok, Ok2: TOverrideCheckFlag;
  begin
    // Find the method name in the current class and base class.
    // The corresponding method of the base class can also be regarded as an implementation.
    Sym := typ.FindSymbol(IntfMeth.Name);
    if (Sym = nil) or (Sym.NodeKind <> nkMethod) then
    begin
      ParseError(IntfMeth.Coord, SErr_IntfMethodNotImpl, [IntfMeth.Name]);
      Exit;
    end;
    ImplMeth := TMethod(Sym);
    Ok2 := cfOk;
    repeat
      Ok := IsImplemented(typ, IntfMeth, ImplMeth);
      if Ok2 = cfOk then
        Break;
      if Ok2 <> cfCannotAccess then
        Ok2 := Ok;
      ImplMeth := TMethod(ImplMeth.NextOverload);
    until ImplMeth = nil;
    if (Ok <> cfOk) then
    begin
      case Ok2 of
        cfCannotAccess: ParseError(typ.Coord, SErr_SymbolNotAccess, [IntfMeth.Name]);
        cfDiffers: ParseError(typ.Coord, SErr_OverridedDiffers, [IntfMeth.Name]);
      end;
    end
    else
      IntfEntry.UpdateVmtEntry(MethIndex, IntfMeth, ImplMeth);
  end;

  procedure CheckIntf(typ: TClassType; IntfEntry: TClassIntfEntry; Intf: TInterfaceType);
  var
    I: integer;
    IntfMeth: TSymbol;
  begin
    for I := 0 to Intf.AllSymbols.Count - 1 do
    begin
      // The current class must implement all methods of this interface including the parent interface
      // Even if the base class has implemented the parent interface, the function that implements the interface is not accessible,
      // Same as unfulfilled
      IntfMeth := Intf.AllSymbols[I];
      if IntfMeth.NodeKind <> nkMethod then
        Continue;
      CheckImplMethods(typ, IntfEntry, I, TMethod(IntfMeth));
    end;
  end;

  procedure CheckMsgMethod(Meth: TMethod);
  var
    A: TFuncParam;
  begin
    if (Meth.ParamCount = 1) then
      A := Meth.Params[0]
    else
      A := nil;
    if (A = nil) or (argVar <> A.Modifier) or (A.ArgKind in [akArrayOfType, akArrayOfConst]) then
    begin
      ParseError(Meth.Coord, SErr_MessageMethodArg);
      Exit;
    end;
    if [fmOverride, fmVirtual] * Meth.Modifiers <> [] then
      ParseError(Meth.Coord, SErr_MessageMethodDirective);
  end;
  {  procedure CheckDup(Result: TClassType; M: TMethod);
    var
      DupSym: TSymbol;
    begin
      while M <> nil do
      begin
        DupSym := Result.FindBaseSymbol(M.Name);
        if DupSym.NodeKind = nkMethod then
          DoCheckDup
        M := TMethod(M.NextOverload);
      end;
    end; }
  procedure CheckClass(typ: TClassType);
  var
    I, Def: integer;
    Sym: TSymbol;
  begin
    if typ.Base <> nil then
    begin
      if caSealed in typ.Base.ClassAttr then
        ParseError(typ.Coord, SErr_BaseClassSealed);
    end;
    Def := 0;
    for I := 0 to typ.Symbols.Count - 1 do
    begin
      Sym := typ.Symbols[I];
      // check virtual function
      case Sym.NodeKind of
        nkMethod:
          if fmOverride in TMethod(Sym).Modifiers then
            CheckOverrides(typ, TMethod(Sym))
          else if fmMessage in TMethod(Sym).Modifiers then
            CheckMsgMethod(TMethod(Sym));
        nkProperty:
          // Check that there can only be one default attribute
          if paDefaultProp in TProperty(Sym).PropAttr then
            Inc(Def);
      end;
    end;
    if Def > 1 then
      ParseError(typ.Coord, SErr_DefaultPropDuplicated);
    // todo 1: Check attribute redeclaration

    // Check the interface implementation
    for I := 0
      to typ.InterfaceCount - 1 do
    begin
      Sym := TSymbol(typ.Interfaces[I]);
      if (TType(Sym).TypeCode = typInterface) then
        CheckIntf(typ, typ.IntfEntries[I], TInterfaceType(Sym));
    end;

   // todo 1: Check for functions with the same name as the base class and the base class is virtual
   { for I := 0 to typ.Members.Count - 1 do
    begin
      Sym := TSymbol(typ.Members[I]);
      if Sym.NodeKind = nkMethod then
        CheckDup(typ, TMethod(Sym));
    end; }

   // todo 1: Check if all abstract methods of the base class are implemented
  {  if (typ.Base <> nil) and (caAbstract in typ.Base.ClassAttr) then
    begin
      for I := 0 to Result.Base.Symbols.Count - 1 do
      begin
        Sym := Result.Symbols[I];
        if Sym.NodeKind <> nkMethod then Continue;
        if fmAbstract in TMethod(Sym).Modifiers then
          ;
      end;
    end;}
  end;

  procedure CheckMethodResolution(typ: TClassType);

    function GetImplMethod(const S: string): TMethod;
    var
      sym: TSymbol;
    begin
      sym := typ.Symbols.Find(S);
      if sym <> nil then
      begin
        if sym.NodeKind <> nkMethod then
          ParseError(SErr_ExpectMethod);
      end
      else
        ParseError(SErr_UndeclaredIdent, [S]);
      Result := TMethod(sym);
    end;

  var
    MR: TMethodResolution;
  begin
    MR := typ.MR;
    while MR <> nil do
    begin
      MR.ImplementingMethod := GetImplMethod(MR.Name);
      MR := TMethodResolution(MR.Next);
    end;
  end;

var
  Field: TField;
  MethSym: TSymbol;
  Prop: TProperty;
  OldErr: integer;
  StateInfo: TParseStateInfo;
  OldParent: TSymbol;
  OldVis: TMemberVisibility;
  ClassPrefix, ClassVar: boolean;
begin
  // NextToken;
  // CurToken is a token after 'class'

  Result := FindForwardClass(TypName);
  if Result <> nil then
  begin
    Exclude(TSymbol(Result).Attr, saForward);
    NotAddSym := True;
  end
  else
  begin
    Result := TClassType(CreateElement(TClassType));
    Result.Name := TypName;
    NotAddSym := False;
  end;
  // forward decl
  if CurToken = tkSemicolon then
  begin
    Include(TSymbol(Result).Attr, saForward);
    Exit;
  end;
  Result.GlobalAlignSize := FAlignSize;
  if psInPacked in FCurStates then
    Result.GlobalAlignSize := 1;
  if FRttiInfo then
    Include(Result.ClassAttr, caRtti);
  StateSet(psInClass, StateInfo);
  if CurToken = tkIdentifier then
  begin
    if SameText(CurTokenString, 'abstract') then
    begin
      Include(Result.ClassAttr, caAbstract);
      NextToken;
    end
    else if SameText(CurTokenString, 'sealed') then
    begin
      Include(Result.ClassAttr, caSealed);
      NextToken;
    end;
  end;
  if CurToken = tkBraceOpen then
    ParseBaseClass(Result);
  if Result.Base = nil then
    Result.Base := FContext.FTObjectType;
  // TMyObj = class(TObject); This case is a complete class definition
  if CurToken = tkSemicolon then
  begin
    StateRestore(StateInfo);
    Exit;
  end;
  OldErr := FErrorCount;
  OldVis := FCurVisibility;
  if Result.RttiEnabled then
    FCurVisibility := visPublished
  else
    FCurVisibility := visPublic;
  ClassPrefix := False;
  ClassVar := False;
  if not NotAddSym then
  begin
    AddSymbol(Result);
    NotAddSym := True;
  end;
  EnterScope(Result.Symbols);
  if FIsSystemUnit and SameText(Result.Name, 'TObject') then
    FContext.FTObjectType := Result;
  OldParent := FCurParent;
  FCurParent := Result;
  while True do
  begin
    case CurToken of
      tkPrivate:
      begin
        FCurVisibility := visPrivate;
        NextToken;
      end;
      tkProtected:
      begin
        FCurVisibility := visProtected;
        NextToken;
      end;
      tkPublic:
      begin
        FCurVisibility := visPublic;
        NextToken;
      end;
      tkPublished:
      begin
        FCurVisibility := visPublished;
        NextToken;
      end;
      tkStrict:
      begin
        NextToken;
        if CurToken = tkPrivate then
          FCurVisibility := visStrictPrivate
        else if CurToken = tkProtected then
          FCurVisibility := visStrictProtected
        else
          ParseError(SErr_ExpectProtectOrPrivate, True);
        NextToken;
      end;
      tkIdentifier:
      begin
        Field := ParseField(TField);
        while Field <> nil do
        begin
          Field.Visibility := FCurVisibility;
          if ClassVar then
            Include(Field.Attr, saStatic);
          AddSymbol(Field);
          Field := TField(Field.Next);
        end;
        Expect(tkSemicolon);
        NextToken;
      end;
      tkVar:
      begin
        NextToken;
        ClassVar := False;
      end;
      tkConst:
      begin
        Self.ParseConstSection(Result);
      end;
      tkType:
      begin
        Self.ParseTypeSection(Result);
      end;
      tkClass:
      begin
        ClassPrefix := True;
        NextToken;
        if CurToken = tkVar then
        begin
          ClassVar := True;
          NextToken;
        end
        else if not (CurToken in [tkFunction, tkProcedure, tkProperty]) then
          ParseError(SErr_ExpectMethodOrProperty, True);
      end;
      tkFunction, tkProcedure, tkConstructor, tkDestructor:
      begin
        // todo 1: Need to increase MethodResolution
        MethSym := ParseFunction(Result);
        case MethSym.NodeKind of
          nkMethod:
          begin
            MethSym.Visibility := FCurVisibility;
            if ClassPrefix then
              Include(MethSym.Attr, saClass);
            if fmStatic in TMethod(MethSym).Modifiers then
              Include(MethSym.Attr, saStatic);
            if (TMethod(MethSym).ID > 0) then
              Result.Symbols.AddOvrld(TMethod(MethSym));
          end;
          nkMethodResolution:
          begin
            if ClassPrefix then
              ParseError(MethSym.Coord, 'Method resolution clause may not need class prefix');
            MethSym.Next := Result.MR;
            Result.MR := TMethodResolution(MethSym);
          end;
        end;
        ClassPrefix := False;
      end;
      tkProperty:
      begin
        Prop := ParseProperty(Result, ClassPrefix);
        Prop.Visibility := FCurVisibility;
        AddSymbol(Prop);
        if ClassPrefix then
          Include(Prop.Attr, saStatic);
        if paDefaultProp in Prop.PropAttr then
          Result.DefaultProp := Prop;
      end;
      tkEnd: Break;
      else
        Expect(tkIdentifier);
    end;
  end;
  Expect(tkEnd);
  NextToken;
  Result.Hints := ParseHints;
  StateRestore(StateInfo);
  LeaveScope;
  FCurParent := OldParent;
  FCurVisibility := OldVis;
  // Check Symbols
  if FErrorCount = OldErr then
  begin
    CheckMethodResolution(Result);
    CheckClass(Result);
  end;
  if FErrorCount = OldErr then
    Result.Update(Self.FPointerSize);
end;

function TParser.ParseCompoundStmt: TCompoundStmt;
var
  Stmt: TStatement;
begin
  NextToken; // skip 'begin'
  Result := TCompoundStmt(CreateStmt(TCompoundStmt));
  Result.IncludeBegin := True;
  while CurToken <> tkEnd do
  begin
    Stmt := ParseStatement(Result);
    if Stmt <> nil then
      Result.Statements.Add(Stmt);
    if CurToken = tkSemicolon then
      NextToken;
  end;
  NextToken; // skip 'end'
end;

procedure TParser.ParseConstArray(Typ: TArrayType; var V: TValueRec);

  procedure ParseConstArrayValue(Typ: TArrayType; var Offset: integer; Value: TArrayValue);
  var
    i: integer;
    isOk: boolean;
    cnt: int64;
    V: TValueRec;
    ValT: TType;
  begin
    Expect(tkBraceOpen);
    NextToken;
    if Typ.ElementType.TypeCode = typArray then
    begin
      ParseConstArrayValue(TArrayType(Typ.ElementType), Offset, Value);
      Expect(tkBraceClose);
      NextToken;
      Exit;
    end;
    with typ.Range do
      cnt := RangeEnd - RangeBegin + 1;
    ValInit(V);
    try
      i := 0;
      while i < cnt do
      begin
        if typ.ElementType.TypeCode = typRecord then
        begin
          ParseConstRecord(TRecordType(typ.ElementType), V);
          isOk := True;
        end
        else
        begin
          isOk := ParseConstSimpleValue(typ.ElementType, V, ValT);
          if isOk then
            isOk := CheckAssignCompatibility(typ.ElementType, ValT);
          // No default value is needed, because the array data will not be referenced by other constants.
          // else
          // ValDefault(V, typ.ElementType);
        end;
        if not isOk or not Value.Put(Offset, V) then
          ParseError(SErr_AssignIncomp);
        Inc(Offset);
        Inc(i);
        if i < cnt then
        begin
          if CurToken = tkBraceClose then
          begin
            ParseError(SErr_NumberOfElementsMismatch, True);
            Break;
          end;
          Expect(tkComma);
          NextToken;
        end;
      end;
    finally
      ValClear(V);
    end;
    if (i >= cnt) and (CurToken = tkComma) then
    begin
      ParseError(SErr_NumberOfElementsMismatch, True);
      Exit;
    end;
    Expect(tkBraceClose);
    NextToken;
  end;

var
  LArrVal: TArrayValue;
  Offset: integer;
begin
  LArrVal := TArrayValue.Create;
  LArrVal.CreateValue(Typ);
  ValFromArray(V, LArrVal);
  Offset := 0;
  ParseConstArrayValue(Typ, Offset, LArrVal);
end;

function TParser.ParseConstExpr: TExpr;
var
  S1: TParseStateInfo;
begin
  StateSet(psInConstExpr, S1);
  Result := ParseExpr;
  StateRestore(S1);
end;

procedure TParser.ParseConstRecord(Typ: TRecordType; var V: TValueRec);

  procedure ParseConstRecordValue(typ: TRecordType; Value: TRecordValue);
  var
    i, fld_index: integer;
    fld: TField;
    valT: TType;
    temp: TValueRec;
  begin
    Expect(tkBraceOpen);
    NextToken;
    ValInit(temp);
    try
      i := 0;
      while i < Value.ElementCount do
      begin
        Expect(tkIdentifier);
        fld := TField(typ.Symbols.Find(Self.CurTokenString));
        if (fld = nil) or (fld.NodeKind <> nkField) then
        begin
          ParseError(SErr_UndeclaredIdent, [Self.CurTokenString], True);
          Break;
        end;
        fld_index := typ.Symbols.IndexOf(fld);
        Assert(fld_index >= 0);
        NextToken;
        Expect(tkColon);
        NextToken;
        ValClear(temp);
        if fld.FieldType.TypeCode = typArray then
        begin
          ParseConstArray(TArrayType(fld.FieldType), temp);
          Value.Put(fld_index, temp);
        end
        else if fld.FieldType.TypeCode = typRecord then
        begin
          ParseConstRecord(TRecordType(fld.FieldType), temp);
          Value.Put(fld_index, temp);
        end
        else if ParseConstSimpleValue(fld.FieldType, temp, valT) then
        begin
          if not CheckAssignCompatibility(fld.FieldType, valT) then
            ParseError(SErr_AssignIncomp);
          Value.Put(fld_index, temp);
        end;
        Inc(i);
        if CurToken = tkBraceClose then
          Break;
        Expect(tkSemiColon);
        NextToken;
      end;
    finally
      ValClear(temp);
    end;
    Expect(tkBraceClose);
    NextToken;
  end;

begin
  ValClear(V);
  V.VRecord := TRecordValue.Create;
  V.VRecord.CreateValue(typ);
  V.VT := vtRecord;
  ParseConstRecordValue(typ, V.VRecord);
end;

procedure TParser.ParseConstSection(Parent: TSymbol);
var
  C: TSymbol;
  Typ, ValTyp: TType;
  //  E: TExpr;
  StateInfo, S2, S3: TParseStateInfo;
begin
  {
  <ConstantDecl>		::= <RefId> '=' <ConstExpr> <OptPortDirectives> ';'
			    | <RefId> ':' <Type> '=' <TypedConstant> <OptPortDirectives> ';'
  }
  NextToken; // skip 'const'
  StateSet(psInVar, StateInfo);
  Expect(tkIdentifier);
  repeat
    FTemp := CurTokenString;
    NextToken;
    if CurToken = tkColon then
    begin
      C := CreateElement(TVariable);
      C.Name := FTemp;
      NextToken;
      Typ := ParseTypeDecl;
      TVariable(C).VarType := Typ;
      Include(TVariable(C).VarAttr, vaReadOnly);
    end
    else
    begin
      C := CreateElement(TConstant);
      C.Name := FTemp;
      Typ := nil;
    end;
    FTemp := '';
    Expect(tkEqual);
    NextToken;
    if C.NodeKind <> nkVariable then
    begin
      StateSet(psNotAllowAddr, S2);
      StateSet(psStopOnErr, S3);
    end;
    C.Visibility := FCurVisibility;
    ValClear(FTempValue);
    // parse init value
    if (C.NodeKind = nkVariable) and (TVariable(c).VarType.TypeCode in [typArray, typRecord]) then
    begin
      if TVariable(c).VarType.TypeCode = typArray then
      begin
        ParseConstArray(TArrayType(TVariable(c).VarType), FTempValue);
        ValClear(TVariable(c).Value);
        TVariable(c).Value.VT := vtArray;
        TVariable(c).Value.VArray := FTempValue.VArray;
        FTempValue.VT := vtEmpty;
      end
      else
      begin
        ParseConstRecord(TRecordType(TVariable(c).VarType), FTempValue);
        ValClear(TVariable(c).Value);
        TVariable(c).Value.VT := vtRecord;
        TVariable(c).Value.VRecord := FTempValue.VRecord;
        FTempValue.VT := vtEmpty;
        //ParseError(c.Coord,'Currently does not support record and array constant expression', True);
      end;
    end
    else if ParseConstSimpleValue(Typ, FTempValue, ValTyp) then
    begin
      if Assigned(Typ) then
      begin
        if not ((Typ.TypeCode = typChar) and (ValTyp.TypeCode = typChar)) and not
          CheckAssignCompatibility(Typ, ValTyp) then
          ParseError(SErr_AssignIncomp);
      end
      else
        TConstant(C).ConstType := ValTyp;
      if C.NodeKind = nkConstant then
        ValCopy(TConstant(C).Value, FTempValue)
      else
        ValCopy(TVariable(C).Value, FTempValue);
      ValClear(FTempValue);
    end
    else
    begin
      if C.NodeKind = nkConstant then
      begin
        // Force the analysis to be aborted. Because this constant may be referenced in multiple places in the future,
        // Unable to determine its value, it is difficult to perform future analysis.
        ParseError(C.Coord, SErr_InvalidConstExpr, True);
      end
      else
        // The analysis fails, give a default value to facilitate the analysis. The default value is not necessary for the variable
        ValDefault(TVariable(C).Value, TVariable(C).VarType);
    end;
    if C.NodeKind <> nkVariable then
    begin
      StateRestore(S2);
      StateRestore(S3);
    end;
    C.Hints := ParseHints;
    Expect(tkSemicolon);
    AddSymbol(C);
    if (C.NodeKind = nkVariable) and (Parent.NodeKind in [nkFunc, nkMethod]) then
      TVariable(C).Level := TFunction(Parent).Level;
    NextToken;
  until CurToken <> tkIdentifier;
  StateRestore(StateInfo);
end;

function TParser.ParseConstSimpleValue(Typ: TType; var Value: TValueRec; out ValTyp: TType): boolean;

  procedure CheckConstRange(Typ: TType; var Value: TValueRec);
  begin
    case typ.TypeCode of
      typInt, typBool, typChar: if IsConstantOutOfRange(typ, Value) then
          ParseError(SErr_ConstantOutOfRange);
    end;
  end;

var
  E: TExpr;
begin
  Result := False;
  E := ParseConstExpr;
  ValClear(Value);
  if CheckConstExpr(E) and TryEvalGet(E, Value) then
  begin  // Must CheckConstExpr, so that Addr will be evaluated correctly
    ValTyp := E.Typ;
    if Assigned(typ) then
      CheckConstRange(typ, Value);
    Result := True;
  end
  else
    ValTyp := E.Typ;
  ReleaseExpr(E);
end;

function TParser.ParseDesignator: TExpr;

  function HasFormatArg(E: TExpr): boolean;
  var
    Ref: TSymbol;
  begin
    Ref := E.GetReference;
    Result := (Ref <> nil) and (Ref.NodeKind = nkBuiltinFunc) and (TBuiltinFunction(Ref).Kind in
      [bfStr, bfWrite, bfWriteln]);
  end;

  function ParseFormatArgs: TListExpr;
  var
    OutE, WidE, DecE: TExpr;
    FmtE: TBinaryExpr;
  begin
    Result := Self.CreateListExpr;
    repeat
      OutE := ParseExpr;
      WidE := nil;
      DecE := nil;
      if CurToken = tkColon then
      begin
        WidE := ParseExpr;
        if CurToken = tkColon then
          DecE := ParseExpr;
      end;
      if WidE = nil then
        Result.Add(OutE)
      else
      begin
        FmtE := CreateBinaryExpr(opFMT, OutE, nil);
        FmtE.Right := CreatebinaryExpr(opFMT, WidE, DecE);
        Result.Add(FmtE);
      end;
      if CurToken = tkBraceClose then
        Break;
      Expect(tkComma);
      NextToken;
    until False;
  end;

var
  L, R: TExpr;
begin
  {
<FieldDesignator>	::= <RefId>
			  | <FieldDesignator> '.' <RefId>
<Designator>		::= <FieldDesignator>
			  | <Designator> '.' <FieldDesignator>
			  | <Designator> '^'
			  | <Designator> '[' <ExprList> ']'
			  | <Designator> '(' <ExprList> ')' !FunctionCall or TypeCast
			  | <Designator> '('  ')'           !FunctionCall
			  | '(' <Designator> ')'
			  | INHERITED <Designator>
}
  if CurToken = tkBraceOpen then
  begin
    NextToken;
    Expect(tkIdentifier);
    Result := ParseDesignator;
    Expect(tkBraceClose);
    NextToken;
    Exit;
  end;
  if CurToken = tkInherited then
  begin
    // inherited has a higher priority:
    // inherited BaseMeth[1]; => (inherited BaseMeth)[1];
    //
    if (psInTypeExpr in FCurStates) or (psInConstExpr in FCurStates) then
      ParseError(SErr_InheritedNotAllow, True);
    NextToken;
    Result := CreateUnaryExpr(opINHERITED);
    if CurToken = tkIdentifier then
    begin
      TUnaryExpr(Result).Operand := CreateSymbolExpr(CurTokenString);
      NextToken;
        {  if CurToken = tkBraceOpen then // parameters
      begin
        NextToken;
        if CurToken = tkBraceClose then
          R := CreateListExpr
        else
          R := ParseExprList;
        TBinaryExpr(Result).Right := R;
        Expect(tkBraceClose);
        NextToken;
      end; }
    end;
  end
  else if CurToken = tkString then
  begin
    Result := CreateSymbolExpr(FContext.FStringType.Name);
    TSymbolExpr(Result).reference := FContext.FStringType;
    NextToken;
  end
  else
  begin
    ParseQualifiedId;
    Result := SimplifyQualId;
    FQId.Reset;
  end;
  while True do
  begin
    case CurToken of
      tkDot:
      begin
        L := Result;
        Result := CreateBinaryExpr(opMEMBER);
        // Allow reserved words to appear after tkDot(.)
        // such as MyUnit.Type
        Scanner.NoReservedWord := True;
        NextToken;
        Scanner.NoReservedWord := False;
        Expect(tkIdentifier);
        R := CreateSymbolExpr(CurTokenString);
        TBinaryExpr(Result).Left := L;
        TBinaryExpr(Result).Right := R;
        NextToken;
      end;
      tkCaret: if (psInTypeExpr in FCurStates) or (psInConstExpr in FCurStates) then
          ParseError(SErr_OpNotAllow, True)
        else
        begin
          L := Result;
          Result := CreateUnaryExpr(opINST, L);
          NextToken;
        end;
      tkBraceOpen:  // Function call or type conversion
      begin
        L := Result;
        Result := CreateBinaryExpr(opCALL);  // Tentatively scheduled as a function call
        if L.IsTypeSymbol then
          Result.OpCode := opCAST;
        NextToken;   // skip '('
        if Result.OpCode = opCAST then
        begin
          if CurToken = tkBraceClose then
            Expect(tkIdentifier);
          R := ParseExpr;
        end
        else if HasFormatArg(L) then
        begin
          if CurToken = tkBraceClose then
            R := CreateListExpr
          else
            R := ParseFormatArgs;
          Include(R.Attr, eaArgList);
        end
        else
        begin
          if CurToken = tkBraceClose then
            R := CreateListExpr
          else
            R := ParseExprList;
          Include(R.Attr, eaArgList);
        end;
        TBinaryExpr(Result).Left := L;
        TBinaryExpr(Result).Right := R;
        Expect(tkBraceClose);
        NextToken;
      end;
      tkSquaredBraceOpen: if (psInTypeExpr in FCurStates) or (psInConstExpr in FCurStates) then
          ParseError(SErr_OpNotAllow, True)
        else
        begin
          NextToken;
          L := Result;
          Result := CreateBinaryExpr(opINDEX);
          if CurToken = tkSquaredBraceClose then
          begin
            R := nil;
            ParseError('Expression expected');
          end
          else
            R := ParseExprList;
          TBinaryExpr(Result).Left := L;
          TBinaryExpr(Result).Right := R;
          Expect(tkSquaredBraceClose);
          NextToken;
        end;
      else
        Break;
    end;
  end;
end;

procedure TParser.ParseError(const Msg: string; Stop: boolean);
var
  Coord: TAstNodeCoord;
begin
  Coord.FileName := Scanner.CurFileName;
  Coord.Row := Scanner.CurRow;
  Coord.Col := Scanner.CurColumn;
  ParseError(Coord, Msg, Stop);
end;

procedure TParser.ParseError(const Msg: string; Args: array of const; Stop: boolean);
begin
  ParseError(Format(Msg, Args), Stop);
end;

procedure TParser.ParseError(const Coord: TAstNodeCoord; const Msg: string; Stop: boolean);
var
  Err: TParserErrorInfo;
begin
  Inc(FErrorCount);
  if FErrorCount > FMaxErrorCount then
    Stop := True;
  if Assigned(FOnError) then
  begin
    Err := TParserErrorInfo.Create;
    Err.Row := Coord.Row;
    Err.Column :=
      Coord.Col;
    Err.FileName := Coord.FileName;
    Err.ErrorMessage := Msg;
    FOnError(Err);
    Err.Free;
    if Stop then
      raise EParseStop.Create(Msg, Coord.FileName, Coord.Row, Coord.Col);
  end
  else
  begin
    raise EParserError.Create(Msg, Coord.FileName, Coord.Row, Coord.Col);
  end;
end;

procedure TParser.ParseError(const Coord: TAstNodeCoord; const Msg: string; Args: array of const; Stop: boolean);
begin
  ParseError(Coord, Format(Msg, Args), Stop);
end;

function TParser.ParseExpr: TExpr;

  function RelOp(T: TToken): TExprOpCode;
  begin
    case T of
      tkLessThan: Result := opLT;
      tkEqual: Result := opEQ;
      tkGreaterThan: Result := opGT;
      tkNotEqual: Result := opNE;
      tkLessEqualThan: Result := opLE;
      tkGreaterEqualThan: Result := opGE;
      tkIs: Result := opIS;
      tkAs: Result := opAS;
      tkIn: Result := opIN;
      else
        Result := opNone;
    end;
  end;

var
  left, right: TExpr;
  op: TExprOpCode;
begin
  {
  <Expr>			::= <AddExpr>
			    | <AddExpr> <RelOp> <AddExpr>
			    | SynError
  }
  Result := ParseAddExpr;
  if psInTypeExpr in FCurStates then
  begin
    // Analysis type expression
    {
    MySubrange = a.b * 2 div 1 .. 100;
    My2 = 1>2..True;
    My3 = sizeof(Integer)..Sizeof(Double)
    }
    if Result.OpCode in [opSYMBOL, opMEMBER] then
      Exit;
  end;
  op := RelOp(CurToken);
  while op <> opNONE do
  begin
    NextToken;
    left := Result;
    right := ParseAddExpr;
    Result := CreateBinaryExpr(op, left, right);
    op := RelOp(CurToken);
  end;
end;

function TParser.ParseExprList: TExpr;
var
  L: TExpr;
begin
  {<ExprList>		::= <Expr>
			  | <ExprList> ',' <Expr>
  }
  // Read the expression list, the number must be >= 1
  Result := CreateListExpr;
  L := ParseExpr;
  TListExpr(Result).Add(L);
  while
    CurToken = tkComma do
  begin
    NextToken;
    L := ParseExpr;
    TListExpr(Result).Add(L);
  end;
end;

function TParser.ParseFactor: TExpr;
var
  L: TExpr;
begin
  {
<Factor>		::= NIL
			  | <ICONST>
			  | <RCONST>
			  | <SCONST>
			  | <Designator>
			  | <SetConstructor>
			  | '@' <Designator>
			  | '@' '@' <Designator> !returns memory address of a procedural variable
			  | '(' <Expr> ')'
			  | '(' <Expr> ')' '^'
			  | '+' <Factor>
			  | '-' <Factor>
			  | NOT <Factor>
}
  case Self.CurToken of
    tkNil:
    begin
      Result := CreateConstExpr(opNIL);
      Result.Typ := FContext.FPointerType;
      TConstExpr(Result).Value := ValFromPtr(nil);
      NextToken;
    end;
    tkIntConst, tkHexConst, tkOctalConst,
    tkFloatConst, tkBinConst, tkStrConst, tkCharConst: Result := ParseLiteral;
    tkPlus:
    begin
      NextToken;
          //  L := ParseFactor;
    //  Result := CreateUnaryExpr(opPOS, L);
      Result := ParseFactor;
    end;
    tkMinus:
    begin
      NextToken;
      L := ParseFactor;
      Result :=
        CreateUnaryExpr(opNEG, L);
    end;
    tkNot:
    begin
      NextToken;
      L := ParseFactor;
      Result := CreateUnaryExpr(opNOT, L);
    end;
    tkBraceOpen:
    begin
      NextToken;
      Result := ParseExpr;
      Expect(tkBraceClose);
      NextToken;
      if CurToken = tkCaret then
      begin
        L := Result;
        Result := CreateUnaryExpr(opINST, L);
        NextToken;
      end;
    end;
    tkSquaredBraceOpen: Result := ParseSetConstructor;
    tkAt: if (psInTypeExpr in FCurStates) or (psNotAllowAddr in FCurStates) then
      begin
        ParseError(SErr_OpNotAllow, True);
      end
      else
      begin
        Result := CreateUnaryExpr(opAddr, nil);
        NextToken;
        if CurToken = tkAt then
        begin
          NextToken;
          Result.OpCode := opDBLADDR;
          TUnaryExpr(L).Operand := ParseDesignator;
        end
        else
          TUnaryExpr(Result).Operand := ParseDesignator;
      end;
    tkIdentifier, tkInherited, tkString: Result := ParseDesignator;
    tkTrue, tkFalse:
    begin
      Result := CreateConstExpr(opCONST);
      TConstExpr(Result).Value := ValFromBool(CurToken = tkTrue);
      NextToken;
    end;
    else
      Expect(tkIdentifier);
      Result := CreateUnaryExpr(opNONE, nil);
  end;
end;

function TParser.ParseField(FieldClass: TSymbolClass): TField;
var
  Field: TField;
  Typ: TType;
  Hints: TMemberHints;
  StateInfo: TParseStateInfo;
begin
  StateSet(psInField, StateInfo);
  Field := TField(ParseIdList(FieldClass));
  Expect(tkColon);
  NextToken;
  Typ := ParseTypeDecl;
  Hints := [];
  //  if CurToken = tkIdentifier then // parse hint
  Hints := ParseHints;
  Result := Field;
  while Field <> nil do
  begin
    Field.FieldType := Typ;
    Field.Hints := Hints;
    Field :=
      TField(Field.Next);
  end;
  StateRestore(StateInfo);
end;

function TParser.ParseForStmt: TForStmt;
var
  E: TSymbol;
  Typ: TType;
  StateInfo: TParseStateInfo;
begin
  NextToken;  // skip 'for'
  Expect(tkIdentifier);
  Typ := nil;
  E := FindSymbol(CurTokenString);
  if E = nil then
    ParseError(SErr_UndeclaredIdent, [CurTokenString])
  else
  begin
    Include(E.Attr, saUsed);
    case E.NodeKind of
      nkVariable: Typ := TVariable(E).VarType;
      nkFuncParam: Typ := TFuncParam(E).ParamType;
      else
        ParseError('%s must be simple local variable', [CurTokenString]);
    end;
    if (Typ <> nil) and not Typ.IsOrdinal then
      ParseError('For loop control variable must be ordinal type', [CurTokenString]);
  end;
  // todo 1: To check that the loop control variable cannot be assigned
  Result := TForStmt(CreateStmt(TForStmt));
  Result.Value := E;
  NextToken;
  Expect(tkAssign);
  NextToken;
  Result.Start := ParseExpr;
  if CurToken = tkDownto then
    Result.Down := True
  else if CurToken = tkTo then
    Result.Down := False
  else
    Expect(tkTo);
  NextToken;
  Result.Stop := ParseExpr;
  // check expression
  if (Typ <> nil) and CheckExpr(Result.Start) and CheckExpr(Result.Stop) then
  begin
    if not CheckAssignCompatibility(Typ, Result.Start.Typ) then
      ParseError(Result.Start.Coord, SErr_IncompatibleTypes);
    if not CheckAssignCompatibility(Typ, Result.Stop.Typ) then
      ParseError(Result.Stop.Coord, SErr_IncompatibleTypes);
  end;
  Expect(tkDo);
  NextToken;
  StateSet(psInForStmt, StateInfo);
  Result.Stmt := ParseStatement(Result);
  StateRestore(StateInfo);
end;

procedure TParser.ParseFuncParamList(Parent: TSymbol; Params: TFuncParamList);
{
<ParmType>  ::= <TypeRef>
            | ARRAY OF <TypeRef>
            | ARRAY OF CONST
            | FILE SynError
}
  function ParseParamType(out ArgKind: TArgumentKind): TType;
  begin
    ArgKind := akNormal;
    case CurToken of
      tkIdentifier, tkString: Result := ParseTypeRef;
      tkArray:
      begin
        NextToken;
        Expect(tkOf);
        NextToken;
        if CurToken = tkConst then
        begin
          Result := FContext.FVarOpenArrayType;
          NextToken;
        end
        else
        begin
          Result := ParseTypeRef;
          if Result = FContext.FVarRecType then
            Result := FContext.FVarOpenArrayType
          else
            Result := GetOpenArrayType(Result);
        end;
        if TOpenArrayType(Result).ElementType.TypeCode = typUntype then
          ArgKind := akArrayOfConst
        else
          ArgKind := akArrayOfType;
      end;
      tkFile:
      begin
        NextToken;
        if CurToken = tkOf then
        begin
          NextToken;
          ParseTypeDecl;
        end;
        ParseError('File type cannot use in here', True);
        Result := FContext.FIntegerType;
      end;
      else
        Result := FContext.FIntegerType;
    end;
  end;

  function ParseParam:
  TFuncParam;
  var
    Param: TFuncParam;
    Typ: TType;
    E: TExpr;
    DefValue: TValueRec;
    HasVal: boolean;
    M: TArgumentModifier;
    ArgKind: TArgumentKind;
  begin
    M := argDefault;
    case CurToken of
      tkVar: M := argVar;
      tkConst: M := argConst;
      tkOut: M := argOut;
    end;
    if M <> argDefault then
      NextToken;
    // parse list
    Param := TFuncParam(ParseIdList(TFuncParam));
    Result := Param;
    if CurToken = tkColon then
    begin
      Expect(tkColon);
      NextToken;
      Typ := ParseParamType(ArgKind);
    end
    else
    begin
      Typ :=
        FContext.FUntype;
      ArgKind := akUntype;
    end;
    if Typ = nil then
      Typ := FContext.FUntype;
    HasVal := False;
    ValInit(DefValue);
    try
      // parse default value
      if CurToken = tkEqual then
      begin
        NextToken;
        E := ParseConstExpr;
        if (ArgKind in [akArrayOfType, akArrayOfConst]) or (Typ.TypeCode = typUntype) then
          ParseError('Argument of this cannot have default values')
        else
        begin
          HasVal := CheckConstExpr(E);
          if HasVal then
          begin
            HasVal := TryEvalGet(E, DefValue);
            if not CheckAssignCompatibility(Typ, E.Typ) then
              ParseError('Assignment incompatibility');
          end;
          ReleaseExpr(E);
        end;
      end;
      // set Param info
      while Param <> nil do
      begin
        if HasVal then
          Param.DefaultValue := ValCopy(DefValue);
        Param.Modifier := M;
        Param.ParamType := Typ;
        Param.ArgKind := ArgKind;
        Param := TFuncParam(Param.Next);
      end;
    finally
      ValClear(DefValue);
    end;
  end;

  procedure CheckDefaultArg(Args: TFuncParamList);
  var
    i: integer;
    Arg: TFuncParam;
    flag: boolean;
  begin
    flag := False;
    for i := 0 to Args.Count - 1 do
    begin
      Arg := TFuncParam(Args[i]);
      if Arg.DefaultValue.VT <> vtEmpty then
        flag := True;
      if flag and (Arg.DefaultValue.VT = vtEmpty) then
      begin
        ParseError(Arg.Coord, 'Default value required for %s', [Arg.Name]);
        Break;
      end;
    end;
  end;

var
  Param: TFuncParam;
  EndToken: TToken;
begin
  if CurToken = tkBraceOpen then
    EndToken := tkBraceClose
  else
    EndToken := tkSquaredBraceClose;
  NextToken; // skip '('
  if CurToken <> EndToken then
  begin
    repeat
      Param := ParseParam;
      while Param <> nil do
      begin
        Param.Parent := Parent;
        Params.Add(Param);
        Param := TFuncParam(Param.Next);
      end;
      if CurToken = tkSemicolon then
        NextToken
      else
        Break;
    until False;
  end;
  Expect(EndToken);
  NextToken;
  CheckDefaultArg(Params);
end;

function TParser.ParseFunction(Parent: TSymbol): TSymbol;

  function FindExists(const S: string): TFunctionDecl;
  var
    E: TSymbol;
  begin
    E := CurSymbols.Find(S);
    if (E <> nil) and (E.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) then
      Result :=
        TFunctionDecl(E)
    else
      Result := nil;
  end;

  function SameFuncDecl(F1: TFunctionDecl; F2: TFunctionHeader): boolean;

    function SameParam(P1, P2: TFuncParam): boolean;
    begin
      // todo 1: To compare function names
      Result := (P1.ParamType = P2.ParamType) and (P1.Modifier = P2.Modifier) and (P1.ArgKind = P2.ArgKind);
    end;

    function SameParams: boolean;
    var
      I: integer;
    begin
      Result := False;
      if F1.ParamCount <> F2.Params.Count then
        Exit;
      for I := 0 to F1.ParamCount - 1 do
        if not SameParam(F1.Params[I], F2.Params[I]) then
          Exit;
      Result := True;
    end;

    function SameCallConv: boolean;
    const
      CCIDs = [idRegister, idPascal, idCDecl, idStdCall, idSafeCall];
    begin
      Result := CCIDs * F2.Directives = [];
      if not Result then
        Result := F1.CallConvention = F2.CallConvention;
    end;

  begin
    Result := ((F2.MethodKind = mkConstructor) or (F1.ReturnType = F2.ReturnType)) and
      SameParams and SameCallConv and (F2.ClassPrefix = (saClass in F1.Attr));
  end;
  {  function FindProperDecl(Func: TFunctionDecl; Header: TFunctionHeader): TFunctionDecl;
    begin
      Result := Func;
      while Result <> nil do
      begin
        if SameFuncDecl(Result, Header) then Exit;
        Result := Result.NextOverload;
      end;
      if Result = nil then
      begin
        // If not found, use the first one so that the analysis can continue
        ParseError('Declaration of %s differs from previous declaration', [Func.Name]);
        Result := Func;
      end;
    end; }

  // Find the declaration that matches the Header, and return true if found, Func is that function
   // return false if not found, Func has not changed
  function FindProperDecl2(var Func: TFunctionDecl; Header: TFunctionHeader): boolean;
  var
    F: TFunctionDecl;
  begin
    Result := True;
    F := Func;
    while
      Func <> nil do
    begin
      if SameFuncDecl(Func, Header) then
        Exit;
      Func := Func.NextOverload;
    end;
    Result := False;
    Func := F;
  end;

  function FindFuncDecl(var Func: TFunctionDecl; Header: TFunctionHeader): boolean;
  var
    E: TSymbol;
  begin
    E := CurSymbols.Find(Header.Name);
    if (E <> nil) and (E.NodeKind in [nkFunc, nkExternalFunc]) then
    begin
      // Find a suitable overload
      Func := TFunctionDecl(E);
      Result := FindProperDecl2(Func, Header);
    end
    else
    begin
      Result := False;
      Func := nil;
    end;
  end;

  function FindMethodDecl(var Func: TFunctionDecl; Header: TFunctionHeader): boolean;
  var
    E: TSymbol;
    I: integer;
  begin
    E := FModule.FindSymbol(Header.Names[0]);
    //    E := FindSymbol(FModule, Header.Names[0]);
    if E = nil then
      ParseError(SErr_UndeclaredIdent, [Header.Names[0]], True);
    if (E.NodeKind <> nkType) or not (TType(E).TypeCode in [typClass, typRecord, typObject]) then
      ParseError('Identifier is not a class, record or object', True);
    for I := 1 to Header.CountOfNames - 1 do
    begin
      if Assigned(E) and (E.NodeKind = nkType) then
      begin
        case TType(E).TypeCode of
          typClass: E := TClassType(E).FindCurSymbol(Header.Names[I]);
          typRecord: E := TRecordType(E).FindSymbol(Header.Names[I]);
          typObject: E := TObjectType(E).FindCurSymbol(Header.Names[I]);
          else
            ParseError(SErr_UndeclaredIdent, [Header.Names[I]], True);
        end;
      end
      else
        Break;
    end;
    if Assigned(E) and (E.NodeKind <> nkMethod) then
      ParseError('Identifier is not a method', True);
    Func := TFunctionDecl(E);
    Result := FindProperDecl2(Func, Header);
  end;

  procedure NotAllowDotted;
  begin
    if FHeader.CountOfNames > 0 then
      ParseError('Error in function declaration', True);
  end;

  procedure AssignInfo(Func: TFunctionDecl; Header: TFunctionHeader);
  var
    I: integer;
  begin
    if Header.Params.Count > 0 then
      Func.CreateParams;
    for I := 0 to Header.Params.Count - 1 do
    begin
      Header.Params[I].Parent := Func;
      Func.Params.Add(Header.Params[I]);
    end;
    Func.ReturnType := Header.ReturnType;
    Func.Name := Header.Name;
    Func.Modifiers := Header.Modifiers;
    Func.CallConvention := Header.CallConvention;
    case
      Func.NodeKind of
      nkExternalFunc:
      begin
        TExternalFunction(Func).FileName := Header.FileName;
        TExternalFunction(Func).RoutineName := Header.RoutineName;
        TExternalFunction(Func).
          RoutineNo := Header.RoutineNo;
      end;
      nkMethod:
      begin
        TMethod(Func).MsgNo := Header.MsgNo;
        TMethod(Func).MethodKind := Header.MethodKind;
        TMethod(Func).ObjectKind := Header.ObjectKind;
        TMethod(Func).DispID := Header.MsgNo;
      end;
    end;
  end;

  function ToMethod(Header: TFunctionHeader): TFunctionDecl;
  begin
    Result := TMethod(CreateElement(TMethod));
    AssignInfo(Result, Header);
  end;

  function ToFunc(Header: TFunctionHeader): TFunctionDecl;
  begin
    if idExternal in Header.Directives then
      Result := TFunctionDecl(CreateElement(TExternalFunction))
    else
      Result := TFunctionDecl(CreateElement(TFunction));
    AssignInfo(Result, Header);
  end;

  function ToMethodResolution(Header: TFunctionHeader; Parent: TSymbol): TMethodResolution;
  var
    typ: TClassType;

    function GetInterfaceMethod: TMethod;
    var
      i: integer;
      intf: TInterfaceType;
      sym: TSymbol;
    begin
      Result := nil;
      for i := 0 to typ.InterfaceCount - 1 do
      begin
        intf := TInterfaceType(typ.Interfaces[i]);
        if SameText(intf.Name, Header.Names[0]) then
        begin
          sym := intf.FindSymbol(Header.Names[1]);
          if sym.NodeKind = nkMethod then
          begin
            Result := TMethod(sym);
            Exit;
          end;
        end;
      end;
    end;

  begin
    if Parent.NodeKind <> nkType then
      typ := nil
    else if TType(Parent).TypeCode = typClass then
      typ := TClassType(Parent)
    else
      typ := nil;
    Result := TMethodResolution(CreateElement(TMethodResolution));
    if typ = nil then
      ParseError('Method resolution only inside class definition')
    else
    begin
      if FHeader.CountOfNames <> 2 then
      begin
        ParseError('Invalid method resolution');
      end;
      Result.Name := Header.ImplementingName;
      Result.InterfaceMethod := GetInterfaceMethod;
    end;
  end;

  procedure EnterClassScope(Owner: TSymbol);
  begin
    if Owner = nil then
      Exit;
    // The case of nested classes has been considered here
    if (Owner.NodeKind = nkType) then
    begin
      EnterClassScope(Owner.Parent);
      case TType(Owner).TypeCode of
        typClass: EnterScope(TClassType(Owner).AllSymbols);
        typObject: EnterScope(TObjectType(Owner).AllSymbols);
        typRecord: EnterScope(TRecordType(Owner).Symbols);
      end;
    end;
  end;

  procedure LeaveClassScope(Owner: TSymbol);
  begin
    if Owner = nil then
      Exit;
    while Owner <> nil do
    begin
      if (Owner.NodeKind = nkType) and (TType(Owner).TypeCode in [typClass, typObject, typRecord]) then
      begin
        LeaveScope;
      end
      else
        Break;
      Owner := Owner.Parent;
    end;
  end;

  procedure CheckFunc(Func: TFunction);
  var
    i: integer;
    sym: TSymbol;
  begin
    for
      i := 0 to Func.LocalSymbols.Count - 1 do
    begin
      sym := Func.LocalSymbols[i];
      if sym.NodeKind = nkFunc then
      begin
        if TFunction(sym).StartStmt = nil then
          ParseError(sym.Coord, SErr_FuncNotImpl, [sym.Name]);
                (*if (faNeedFPArg in TFunction(sym).FuncAttr) {and (Func.Level > 0)} then
          Include(Func.FuncAttr, faNeedFP);*)
      end;
    end;
  end;

var
  I: integer;
  V: TVariable;
  Func: TFunctionDecl;
  OldFunc: TFunction;
  OldParent: TSymbol;
  ParentTyp: TType;
  StateInfo: TParseStateInfo;
  ClassPrefix: boolean;
begin
  ClassPrefix := psInClassPrefix in FCurStates;
  if ClassPrefix then
    Exclude(FCurStates, psInClassPrefix);
  StateSet(psInFunc, StateInfo);
  ParseFunctionHeader(FHeader);
  StateRestore(StateInfo);
  FHeader.ClassPrefix := ClassPrefix;
    // in class / object / record
  // in interface section
  // in implement section
  if FHeader.ImplementingName <> '' then
  begin
    // is a method parsing statement
    Result := ToMethodResolution(FHeader, Parent);
    FHeader.Reset;
    Exit;
  end;
  // todo 2: Where the function is implemented, the parameter list can be omitted.
  //   Not if there is overload
  // todo 2: The implementation here is the same as the $mode objpas of fpc, that is,
  //   the implementation part cannot omit the parameters. It will be compatible with delphi in the future
  if Parent.NodeKind = nkType then
    ParentTyp := TType(Parent)
  else
    ParentTyp := nil;
  if Assigned(ParentTyp) then
  begin
    case ParentTyp.TypeCode of
      typClass: FHeader.ObjectKind := okClass;
      typObject: FHeader.ObjectKind := okObject;
      typRecord: FHeader.ObjectKind := okRecord;
    end;
    if FHeader.MethodKind = mkConstructor then
      FHeader.ReturnType := TType(ParentTyp);
  end;
  // find the declared
  if FCurStates * [psInClass, psInRecord, psInObject, psInIntf, psInDispIntf] <> [] then
  begin
    // In the declaration part of class, record, object, interface, dispinterface
    NotAllowDotted;
    Func := FindExists(FHeader.Name);
    Result := ToMethod(FHeader);
    if (Func <> nil) then
    begin
      if CheckOverloads(Func, TFunctionDecl(Result)) then
      begin
        TFunctionDecl(Result).ID :=
          Func.ID + 1;
        Func.AddOverload(TFunctionDecl(Result));
      end;
      Result.Parent := Parent;
    end
    else
    begin
      AddSymbol(Result);
    end;
    // Constructor/destructor will not be analyzed when analyzing interface/dispinterface
  {  if (FHeader.MethodKind in [mkConstructor, mkDestructor])
      and Assigned(ParentTyp) and not (ParentTyp.TypeCode in [typClass, typObject, typRecord]) then
    begin
      ParseError(Result.Coord, SErr_IntfNotAllowCtorDtor);
    end;}
    Include(TFunctionDecl(Result).Modifiers, fmForward);
  end
  else if psInIntfSect in FCurStates then
  begin
    // In the interface section, it can only be functions and procedures, not methods
    NotAllowDotted;
    Func := FindExists(FHeader.Name);
    Result := ToFunc(FHeader);
    if Func <> nil then
    begin
      if CheckOverloads(Func, TFunctionDecl(Result)) then
      begin
        TFunctionDecl(Result).ID := Func.ID + 1;
        Func.AddOverload(TFunctionDecl(Result));
      end;
      Result.Parent := Parent;
    end
    else
    begin
      AddSymbol(Result);
    end;
    Include(TFunctionDecl(Result).Modifiers, fmForward);
  end
  else
  begin
    // todo 2: It is necessary to consider that the method has been implemented,
    // and the error code for another implementation
    Assert(psInImplSect in FCurStates);
    if FHeader.CountOfNames > 1 then
    begin
      // method
      if FindMethodDecl(Func, FHeader) then
        Result := Func  // todo 1: Consider that this Func has already been implemented
      else
      begin
        Result := ToMethod(FHeader);
        if Func <> nil then
        begin
          TFunctionDecl(Result).ID := Func.ID + 1;
          Func.AddOverload(TFunctionDecl(Result));
          Result.Parent := Func.Parent;
        end;
        ParseError('Method declaration not found', Func = nil);
      end;
      // If there are multiple declarations, but none of them match, an error is reported,
      // but a new method is created to continue the analysis
      Exclude(TFunctionDecl(Result).Modifiers, fmForward);
    end
    else
    begin
      // If multiple declarations are found, but they do not meet, create a new function,
      // This is a new function defined in the implementation section, not an error
      if FindFuncDecl(Func, FHeader) then
      begin
        Result := Func;
        Exclude(TFunctionDecl(Result).Modifiers, fmForward);
      end
      else
      begin
        Result := ToFunc(FHeader);
        //  Result.IsInternal := True;
        if Func <> nil then
        begin
          if CheckOverloads(Func, TFunctionDecl(Result)) then
          begin
            TFunctionDecl(Result).ID := Func.ID + 1;
            Func.AddOverload(TFunctionDecl(Result));
          end;
          Result.Parent := Parent;
        end
        else
        begin
          AddSymbol(Result);
        end;
      end;
    end;
  end;
  FHeader.Reset;
  // todo 1: Overload needs to be checked here.
  if fmForward in TFunctionDecl(Result).Modifiers then
    Exit;
  if fmExternal in TFunctionDecl(Result).Modifiers then
    Exit;
  if TFunction(Result).StartStmt <> nil then
  begin
    ParseError(Result.Coord, 'function definition duplicated');
    TFunction(Result).LocalSymbols.Clear;
    TFunction(Result).StartStmt := nil;
  end;
  StateSet(psInFunc, StateInfo);
  if (Result.NodeKind = nkMethod) then
    EnterClassScope(Result.Parent);
  // local symbols
  EnterScope(TFunction(Result).LocalSymbols);
  if (Result.NodeKind = nkMethod) and Assigned(Result.Parent) and not
    (fmStatic in TFunctionDecl(Result).Modifiers) then
  begin
    V := TVariable(CreateElement(TVariable));
    if saClass in Result.Attr then
      V.VarType := TClassType(Result.Parent).GetClassRef
    else
      V.VarType := TType(Result.Parent);
    V.Name := 'Self';
    V.VarAttr := [vaReadOnly, vaSelf, vaLocal];
    Include(V.Attr, saUsed);
    AddSymbol(V);
  end;
  if TFunctionDecl(Result).ReturnType <> nil then
  begin
    V := TVariable(CreateElement(TVariable));
    V.VarType := TFunctionDecl(Result).ReturnType;
    V.VarAttr := [vaResult, vaLocal];
    V.Attr := [saUsed];
    V.Name := 'Result';
    AddSymbol(V);
  end;
  OldFunc := fCurFunction;
  FCurFunction := TFunction(Result);
  OldParent := FCurParent;
  FCurParent := Result;
  if FTopFunction = nil then
    FTopFunction := FCurFunction;
  if OldFunc <> nil then
    FCurFunction.Level := OldFunc.Level + 1
  else
    FCurFunction.Level := 0;
  for I := 0 to TFunctionDecl(Result).ParamCount - 1 do
  begin
    TFunctionDecl(Result).Params[I].Level := FCurFunction.Level;
    AddSymbol(TFunctionDecl(Result).Params[I]);
  end;
  ParseFunctionBlock(TFunction(Result));
  FCurFunction := OldFunc;
  if FCurFunction = nil then
    FTopFunction := nil;
  FCurParent := OldParent;
  LeaveScope;
  if Result.NodeKind = nkMethod then
    LeaveClassScope(Result.Parent);
  StateRestore(StateInfo);
  CheckFunc(TFunction(Result));
end;

procedure TParser.ParseFunctionBlock(Func: TFunction);
//var
//  OldErr: Integer;
begin
  //  OldErr := FErrorCount;
  while True do
  begin
    case CurToken of
      tkType: Self.ParseTypeSection(Func);
      tkVar: Self.ParseVarSection(Func);
      tkConst: Self.ParseConstSection(Func);
      tkProcedure, tkFunction: Self.ParseFunction(
          Func);
      tkLabel: Self.ParseLabelSection(Func);
      tkResourceString: Self.ParseResStringSection(Func);
      tkThreadVar: ParseError('thread var can not in local', True);
      else
        Expect(tkBegin);
        Func.StartStmt := ParseCompoundStmt;
        Expect(tkSemicolon);
        NextToken;
        Break;
    end;
  end;
  // Check the statement
  CheckFunction(Func);
  // Generate code
  //  if (Func.Level = 1) and (OldErr = FErrorCount) then
  //    FContext.GenCode(Func);
end;

procedure TParser.ParseFunctionDirective(Result: TFunctionHeader);

  procedure ParseExternal;
  begin
    NextToken; // skip 'external'
    if CurToken = tkSemicolon then
      Exit;
    if (CurToken = tkIdentifier) and SameText(CurTokenString, 'name') then
    begin
      NextToken;
      Result.RoutineName := ParseStrExpr('1');
    end
    else
    begin
      Result.FileName := ParseStrExpr('1');
      //      NextToken;
    end;
    if CurToken = tkSemicolon then
      Exit;
    if SameText(CurTokenString, 'name') then
    begin
      NextToken;  // skip 'name'
      Result.RoutineName := ParseStrExpr('1');
    end
    else if SameText(CurTokenString, 'index') then
    begin
      NextToken;  // skip 'index'
      Result.RoutineNo := ParseIntExpr;
    end
    else
      ParseError('name or index expected', True);
    if Result.RoutineName = '' then
      Result.RoutineName := Result.Name;
  end;

  procedure SetFlag(Result: TFunctionHeader; D: TDirectiveIdent);
  begin
    Include(Result.Directives, D);
    if D in [idDeprecated..idUnimplemented] then
      Include(Result.Hints, TMemberHint(Ord(D) - Ord(idDeprecated)))
    else if D in [idRegister..idSafeCall] then
      Result.CallConvention := TCallingConvention(Ord(D) - Ord(idRegister) + 1)
    else
      Include(Result.Modifiers, TFunctionModifier(Ord(D) - Ord(idVirtual)));
  end;

var
  Directive: TDirectiveIdent;
begin
  {object pascal commands have a certain order, which can be separated by
  semicolons or not. Regardless of the order here, semicolons are optional.

  <CallDirectives>  ::= <CallDirective>
                    | <CallDirectives> <CallDirective>

  <CallDirective>   ::= register | pascal | cdecl | stdcall | safecall |
                      inline | near | far | export | assmebler |
                      local | varargs | overload |
                      forward | external
  }
  // Instructions do not need to be used; separated from functions
  while True do
  begin
    if CurToken = tkSemicolon then
      Break;
    Directive := FindDirective(CurTokenString);
    if (Directive in [idNone, idForward, idExternal]) then
      ParseError('Invalid function directive: %s', [CurTokenString], True)
    else
    begin
      SetFlag(Result, Directive);
    end;
    NextToken;
  end;
  Expect(tkSemicolon);
    // analyse CallDirectives
  while True do
  begin
    if CurToken = tkSemicolon then
      NextToken;
    if CurToken in [tkVar, tkConst, tkResourceString, tkType, tkLabel, tkClass, tkProperty,
      tkProcedure, tkFunction, tkConstructor, tkDestructor, tkBegin, tkEnd, tkImplementation,
      tkPrivate, tkProtected, tkPublic, tkPublished, tkStrict] then
      Break;
    Directive := FindDirective(CurTokenString);
    case Directive of
      idExternal:  // external has to be the last one
      begin
        SetFlag(Result, Directive);
        ParseExternal;
        if CurToken = tkSemicolon then
          NextToken;
        Break;
      end;
      idMessage:
      begin
        NextToken;
        Result.MsgNo := ParseIntExpr;
        SetFlag(Result, Directive);
      end;
      idDispMId:
      begin
        NextToken;
        Result.DispID := ParseIntExpr;
        SetFlag(Result, Directive);
      end;
      idNone:
      begin
        NextToken;
        ParseError('Invalid function directive: %s', [CurTokenString]);
      end;
      else
        SetFlag(Result, Directive);
        NextToken;
    end;
    //    NextToken;
  end;
end;

procedure TParser.ParseFunctionHeader(Result: TFunctionHeader);

  procedure GetDottedNames(Func: TFunctionHeader);
  var
    I: integer;
  begin
    I := 1;
    NextToken; // skip '.'
    repeat
      Expect(tkIdentifier);
      with Func do
        if I >= Length(Names) then
          SetLength(Names, Length(Names) + 10);
      Func.Names
        [I] := CurTokenString;
      Inc(I);
      NextToken;
      if CurToken <> tkDot then
        Break;
      NextToken;
    until
      False;
    Func.CountOfNames := I;
    with Func do
      Names[0] := Name;
  end;

var
  IsProc: boolean;
begin
  {
  <FunctionDecl>  ::= <FuncHeading>  <CallBody> <OptSemi>
  <FuncHeading>   ::= FUNCTION  <RefId> <OptFormalParms> ':' <ResultType> <OptCallSpecifiers> ';'
                  | FUNCTION  <RefId> ';'
                  | <FuncHeading> <CallDirectives> <OptSemi>

  <CallBody>    ::= <OptDeclSection> <CompoundStmt>
                | <OptDeclSection> <AssemblerStmt>
                | <ExternalDeclaration>
                | FORWARD
  }
  IsProc := CurToken <> tkFunction;
  if CurToken = tkConstructor then
    Result.MethodKind := mkConstructor
  else if CurToken = tkDestructor then
    Result.MethodKind := mkDestructor
  else
    Result.MethodKind := mkNormal;
  NextToken; // skip 'function' / 'procedure' / 'constructor' / 'destructor'
  Expect(tkIdentifier);
  Result.Name := CurTokenString;
  NextToken;
  if CurToken = tkDot then
    GetDottedNames(Result);
  if CurToken = tkBraceOpen then
  begin
    ParseFuncParamList(nil, Result.Params);
  end
  else if CurToken = tkEqual then
  begin
    NextToken;
    Expect(tkIdentifier);
    Result.ImplementingName := CurTokenString;
    NextToken;
    Expect(tkSemicolon);
    NextToken;
    Exit;
  end;
  if not IsProc then
  begin
    // parse return type
    Expect(tkColon);
    if CurToken = tkColon then
      NextToken;
    Result.ReturnType := ParseTypeRef;
  end;
  ParseFunctionDirective(Result);
  // Convert dynamic to virtual
  if fmDynamic in Result.Modifiers then
  begin
    Exclude(Result.Modifiers, fmDynamic);
    Include(Result.Modifiers, fmVirtual);
  end;
end;

function TParser.ParseGotoStmt: TGotoStmt;
var
  E: TSymbol;
begin
  Result := TGotoStmt(CreateStmt(TGotoStmt));
  NextToken;  // skip 'goto';
  if CurToken in [tkIdentifier, tkIntConst] then
  begin
    E := FindSymbol(CurTokenString);
    if E = nil then
      ParseError(SErr_UndeclaredIdent)
    else if E.NodeKind <> nkLabel then
      ParseError(SErr_LabelExpected)
    else
      Result.StmtLabel := TStmtLabel(E);
    NextToken;
    //  Expect(tkSemicolon);
  end
  else
    Expect(tkIdentifier);
end;

function TParser.ParseHints: TMemberHints;
var
  S: string;
begin
  // Cur is tkIdentifier
  Result := [];
  repeat
    if CurToken = tkIdentifier then
    begin
      S := CurTokenString;
      if SameText(S, 'deprecated') then
        Include(Result, hDeprecated)
      else if SameText(S, 'platform') then
        Include(Result, hPlatform)
      else if SameText(S, 'experimental') then
        Include(Result, hExperimental)
      else if SameText(S, 'unimplemented') then
        Include(Result, hUnimplemented)
      else
        Break;
    end
    else if CurToken = tkLibrary then
      Include(Result, hLibrary)
    else
      Break;
    NextToken;
  until False;
end;

function TParser.ParseIdList(SymClass: TSymbolClass): TSymbol;
var
  E1, E2: TSymbol;
begin
  // cur token must be tkIdentifier
  Result := nil;
  E2 := nil;
  repeat
    Expect(
      tkIdentifier);
    E1 := TSymbol(CreateElement(SymClass));
    E1.Name := CurTokenString;
    if Result = nil then
      Result := E1;
    if E2 <> nil then
      E2.Next := E1;
    E2 := E1;
    NextToken;
    if CurToken <> tkComma then
      Break;
    NextToken;
  until False;
end;

function TParser.ParseIfStmt: TIfStmt;
begin
  NextToken;  // skip if
  Result := TIfStmt(CreateStmt(TIfStmt));
  Result.Value := ParseExpr;
  CheckBoolExpr(Result.Value);
  Expect(tkThen);
  NextToken;
  Result.TrueStmt := ParseStatement(Result);
  if CurToken = tkElse then
  begin
    NextToken;
    Result.FalseStmt := ParseStatement(Result);
  end;
end;

procedure TParser.ParseImplementSection;

  procedure ParseStmtList(Stmts: TCompoundStmt);
  var
    Stmt: TStatement;
  begin
    while not (CurToken in [tkEnd, tkFinalization]) do
    begin
      Stmt := ParseStatement(Stmts);
      if Stmt <> nil then
        Stmts.Statements.Add(Stmt);
      if CurToken = tkSemicolon then
        NextToken;
    end;
  end;

  function ParseCodeList: TCompoundStmt;
  begin
    Result := TCompoundStmt(CreateStmt(TCompoundStmt));
    ParseStmtList(Result);
  end;

  function ParseEntryCode(const AName: TSymString): TFunction;
  var
    StateInfo: TParseStateInfo;
  begin
    Result := TFunction(CreateElement(TFunction));
    Exclude(Result.Attr, saInternal);
    Result.Name := AName;
    Result.Parent := FModule;
    FCurFunction := Result;
    StateSet(psInFunc, StateInfo);
    Result.StartStmt := ParseCodeList;
    StateRestore(StateInfo);
    FCurFunction := nil;
  end;

  function CreateEmptyFunc(const aName: TSymString): TFunction;
  begin
    Result := TFunction(CreateElement(TFunction));
    Exclude(Result.Attr, saInternal);
    Result.Name := AName;
    Result.Parent := FModule;
    Result.StartStmt := TCompoundStmt(CreateStmt(TCompoundStmt));
  end;

begin
  {
  <ImplementationSection> ::= IMPLEMENTATION <OptUsesSection> <OptDeclSection> <OptExportBlock>
  }
  FCurStates := [psInImplSect];
  FInternalSection := True;
  NextToken;   // skip 'implementation'
  if CurToken = tkUses then
    ParseUsesClause;
  while True do
  begin
    case CurToken of
      tkType: Self.ParseTypeSection(FModule);
      tkVar, tkThreadVar: Self.ParseVarSection(FModule);
      tkConst: Self.ParseConstSection(FModule);
      tkResourceString: Self.ParseResStringSection(FModule);
      tkProcedure, tkFunction, tkConstructor, tkDestructor: Self.ParseFunction(FModule);
      tkClass:
      begin
        NextToken;
        if CurToken in [tkProcedure, tkFunction] then
        begin
          Include(Self.FCurStates, psInClassPrefix);
          Self.ParseFunction(FModule);
        end
        else
          ParseError(SErr_ExpectProcOrFunc, True);
      end;
      tkLabel: Self.ParseLabelSection(FModule);
      else
        Break;
    end;
  end;
  if CurToken = tkInitialization then
  begin
    NextToken;
    FModule.InitializeFunc := ParseEntryCode('$init');
    if CurToken = tkFinalization then
    begin
      NextToken;
      FModule.FinalizeFunc := ParseEntryCode('$final');
    end;
    Expect(tkEnd);
    NextToken;
  end
  else if CurToken = tkBegin then
  begin
    NextToken;
    FModule.InitializeFunc := ParseEntryCode('$init');
    Expect(tkEnd);
    NextToken;
  end
  else
  begin
    Expect(tkEnd);
    NextToken;
  end;
  // Create a blank initialization/finalization function
  if FModule.InitializeFunc = nil then
    FModule.InitializeFunc := CreateEmptyFunc('$init');
  if FModule.FinalizeFunc = nil then
    FModule.FinalizeFunc := CreateEmptyFunc('$final');
  Expect(tkDot);
end;

procedure TParser.ParseInterfaceSection;
begin
  {
  <InterfaceSection>	::= INTERFACE <OptUsesSection> <OptExportDeclList>
  }
  FCurStates := [psInIntfSect];
  NextToken; // skip 'interface'
  if CurToken = tkUses then
    ParseUsesClause;
  while True do
  begin
    case CurToken of
      tkType: Self.ParseTypeSection(FModule);
      tkVar: Self.ParseVarSection(FModule);
      tkConst: Self.ParseConstSection(FModule);
      tkResourceString: Self.ParseResStringSection(FModule);
      tkProcedure, tkFunction: Self.ParseFunction(FModule);
      tkLabel:
      begin
        ParseError('Label declaration not allowed in interface part'); //Self.ParseLabelSection(FModule);
        Self.ParseLabelSection(FModule);
      end;
      else
        Break;
    end;
  end;
end;

function TParser.ParseInterfaceType(const IntfName: string; Parent: TSymbol; out NotAddSym: boolean): TInterfaceType;

  procedure ParseGuidConst(var guid: TGuid);
  begin
    try
      guid := StringToGuid(ParseStrExpr('{00000000-0000-0000-C000-000000000046}'));
    except
      ParseError('Invalid guid string');
    end;
  end;

  function FindForwardIntf(const S: string): TInterfaceType;
  var
    E: TSymbol;
  begin
    E := CurSymbols.Find(S);
    if Assigned(E) and (E.ClassType = TInterfaceType) and (saForward in E.Attr) then
      Result := TInterfaceType(E)
    else
      Result := nil;
  end;

  procedure CheckIntf(Typ: TInterfaceType);
  var
    i, Def: integer;
    Sym: TSymbol;
  begin
    Def := 0;
    for i := 0 to Typ.Symbols.Count - 1 do
    begin
      Sym := Typ.Symbols[i];
      if Sym.NodeKind = nkIntfProperty then
        if ipaDefaultProp in TIntfProperty(Sym).PropAttr then
          Inc(Def);
    end;
    if Def > 1 then
      ParseError(Typ.Coord, 'Only one default property can inside class,object,record,interface declaration');
  end;

var
  Typ: TType;
  OldErr: integer;
  MethSym: TSymbol;
  Prop: TIntfProperty;
  OldParent: TSymbol;
  State: TParseStateInfo;
begin
  Result := FindForwardIntf(IntfName);
  if Result <> nil then
  begin
    if Result.IsDisp <> (CurToken = tkDispInterface) then
      ParseError(SErr_RedeclaredIdent, [IntfName]);
    Exclude(Result.Attr, saForward);
    NotAddSym := True;
  end
  else
  begin
    Result := TInterfaceType(CreateElement(TInterfaceType));
    Result.Name := IntfName;
    Result.IsDisp := CurToken = tkDispInterface;
    NotAddSym := False;
  end;
  NextToken;  // skip 'interface'
  OldErr := FErrorCount;
  if CurToken = tkSemicolon then
  begin  // forward
    Include(Result.Attr, saForward);
    Exit;
  end;
  if Result.IsDisp then
    StateSet(psInDispIntf, State)
  else
    StateSet(psInIntf, State);
  if CurToken = tkBraceOpen then
  begin
    // parse base
    NextToken;
    Typ := ParseTypeRef;
    Typ := Typ.OriginalType;
    if Typ.TypeCode <> typInterface then
      ParseError(SErr_InvalidBaseIntf)
    else
      Result.Base := TInterfaceType(Typ);
    Expect(tkBraceClose);
    NextToken;
  end;
  // The dispinterface base class is idispinterface
  if Result.Base = nil then
  begin
    if Result.IsDisp then
      Result.Base := FContext.FIDispatchType
    else
      Result.Base := FContext.FIUnknownType;
  end;
  // The dispinterface must have a GUID, but the interface does not have to be a GUID
  if CurToken = tkSquaredBraceOpen then
  begin
    NextToken;
    ParseGuidConst(Result.Guid);
    Expect(tkSquaredBraceClose);
    NextToken;
  end
  else if Result.IsDisp then
    Expect(tkSquaredBraceOpen);
  if not NotAddSym then
  begin
    AddSymbol(Result);
    NotAddSym := True;
  end;
  OldParent := FCurParent;
  FCurParent := Result;
  if FIsSystemUnit then
    if SameText(Result.Name, 'IInterface') then
      FContext.FIUnknownType := Result
    else if SameText(Result.Name, 'IDispatch') then
      FContext.FIDispatchType := Result;
  Self.EnterScope(Result.Symbols);
  while True do
  begin
    case
      CurToken of
      tkProcedure, tkFunction:
      begin
        MethSym := Self.ParseFunction(Result);
        if MethSym.NodeKind <> nkMethod then
          ParseError(MethSym.Coord, 'Method required');
        Exclude(TFunctionDecl(MethSym).Modifiers, fmForward);
        if Result.IsDisp then
          if not (fmDispID in TMethod(MethSym).Modifiers) then
            ParseError('DispID is required for method or property of dispinterface');
        if (MethSym.NodeKind = nkMethod) and (fmOvrldFlag in TMethod(MethSym).Modifiers) then
        begin
          Result.Symbols.AddOvrld(TMethod(MethSym));
        end;
      end;
      tkProperty:
      begin
        Prop := ParseIntfProperty(Result);
        AddSymbol(Prop);
        if ipaDefaultProp in Prop.PropAttr then
          Result.DefaultProp := Prop;
        if Result.IsDisp then
          if not (ipaHasDispID in Prop.PropAttr) then
            ParseError('DispID is required for method or property of dispinterface');
      end;
      tkVar, tkConst,
      tkType: ParseError('var, const and type not allow in interface');
      tkEnd: Break;
      else
        Expect(tkEnd);
    end;
  end;
  Expect(tkEnd);
  NextToken;
  Result.Hints := ParseHints;
  FCurParent := OldParent;
  StateRestore(State);
  Self.LeaveScope;
  if OldErr = FErrorCount then
    CheckIntf(Result);
  if OldErr = FErrorCount then
    Result.UpdateVmt;
end;

function TParser.ParseIntExpr(const DefValue: integer): integer;
var
  E: TExpr;
  V: TValueRec;
begin
  E := ParseConstExpr;
  if CheckConstExpr(E) and E.Typ.IsInteger then
  begin
    ValInit(V);
    if TryEvalGet(E, V) then
      Result := ValToInt(V)
    else
      Result := DefValue;
    ValClear(V);
  end
  else
  begin
    ParseError('Integer constant expression expected');
    Result := DefValue;
  end;
end;

function TParser.ParseIntfProperty(Parent: TType): TIntfProperty;

  function ParseAccessor: TMethod;
  var
    E: TSymbol;
  begin
    Expect(tkIdentifier);
    E := CurSymbols.Find(CurTokenString);
    if (E.NodeKind = nkMethod) and (E.Parent = Parent) then
      Result := TMethod(E)
    else
    begin
      Result := nil;
      ParseError('Invalid property accessor');
    end;
    NextToken;
  end;

  function ExpectParentType(IsDisp: boolean): boolean;
  begin
    Result := (Parent.TypeCode = typInterface) and (TInterfaceType(Parent).IsDisp = IsDisp);
    if not Result then
      ParseError('property directive not allow in here');
  end;

  function IsSameType(t1, t2: TType): boolean;
  begin
    t1 := t1.OriginalType;
    t2 := t2.OriginalType;
    if t1.TypeCode = typSubrange then
      t1 := TSubrangeType(t1).BaseType;
    if t2.TypeCode = typSubrange then
      t2 := TSubrangeType(t2).BaseType;
    Result := t1 = t2;
  end;

  procedure CheckSetterArgs(Prop: TIntfProperty; MethodArgs: TFuncParamList);
  var
    I, ExpectArgCount: integer;
    A1, A2: TFuncParam;
  begin
    ExpectArgCount := Prop.ParamCount + 1;
    if (MethodArgs = nil) or (MethodArgs.Count <> ExpectArgCount) then
      ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched)
    else
    begin
      { Setter:
        procedure SetValue(i: Integer; value: Double);
      }
      for I := 0 to Prop.ParamCount - 1 do
      begin
        A1 := Prop.Params[I];
        A2 := MethodArgs[I];
        if not IsSameType(A1.ParamType, A2.ParamType) or (A1.Modifier <> A2.Modifier) then
        begin
          ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
          Exit;
        end;
      end;
      A1 := MethodArgs[MethodArgs.Count - 1];
      if not IsSameType(Prop.PropType, A1.ParamType) or (A1.Modifier in [argVar, argOut]) then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end;
  end;

  procedure CheckSetter(Prop: TIntfProperty);
  begin
    if Prop.Setter = nil then
      Exit;
    if Prop.Setter.ReturnType <> nil then
      ParseError(Prop.Coord, 'Setter method not allow return value')
    else
      CheckSetterArgs(Prop, TMethod(Prop.Setter).Params);
  end;

  procedure CheckGetterArgs(Prop: TIntfProperty; MethodArgs: TFuncParamList);
  var
    I, ExpectArgCount: integer;
    A1, A2: TFuncParam;
  begin
    ExpectArgCount := Prop.ParamCount;
    if MethodArgs = nil then
    begin
      if ExpectArgCount <> 0 then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end
    else
      for I := 0 to Prop.ParamCount - 1 do
      begin
        A1 := Prop.Params[I];
        A2 := MethodArgs[I];
        if not IsSameType(A1.ParamType, A2.ParamType) or (A1.Modifier <> A2.Modifier) then
        begin
          ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
          Exit;
        end;
      end;
  end;

  procedure CheckGetter(Prop: TIntfProperty);
  begin
    if Prop.Getter = nil then
      Exit;
    if not IsSameType(Prop.PropType, Prop.Getter.ReturnType) then
      ParseError(Prop.Coord, 'Accessor type not matched')
    else
      CheckGetterArgs(Prop, Prop.Getter.Params);
  end;

  procedure CheckProp(Prop: TIntfProperty);
  var
    OldErr: integer;
  begin
    if (ipaDefaultProp in Prop.PropAttr) and (Prop.ParamCount = 0) then
      ParseError(Prop.Coord, 'Non-array property not allow default directive')
    else
    begin
      OldErr := FErrorCount;
      CheckGetter(Prop);
      if OldErr = FErrorCount then
        CheckSetter(Prop);
    end;
  end;

var
  PropD: TPropDirective;
  OldErr: integer;
begin
{
<PropertySpec>		::= PROPERTY <PropertyDecl> <OptPropSpecifiers> ';'

<PropertyDecl>		::= <RefId>                     ':' <TypeRef>
			  | <RefId> '[' <IndexList> ']' ':' <TypeRef>
			  | <RefId>
<PropertySpecifiers>	::= <PropertySpecifier>
			  | <PropertySpecifiers>  <PropertySpecifier>

<PropertySpecifier>	::= READ       <FieldDesignator>
			  | WRITE      <FieldDesignator>
			  | WRITEONLY
			  | READONLY
			  | DISPID <ConstIntExpr>        !Only within InterfaceTypes
}
  NextToken;
  Expect(tkIdentifier);
  Result := TIntfProperty(CreateElement(TIntfProperty));
  Result.Name := CurTokenString;
  NextToken;
  OldErr := FErrorCount;
  if CurToken = tkSquaredBraceOpen then
  begin
    NextToken;
    // parse array property args
    Result.CreateParams;
    Self.ParseFuncParamList(Result, Result.Params);
    Expect(tkColon);
  end;
  if CurToken = tkColon then
  begin
    NextToken;
    Result.PropType := ParseTypeRef;
  end;
  while CurToken = tkIdentifier do
  begin
    PropD := ParsePropDirective(CurTokenString);
    NextToken;
    case PropD of
      idRead: if ExpectParentType(False) then
          Result.Getter := ParseAccessor;
      idWrite: if ExpectParentType(False) then
          Result.Setter := ParseAccessor;
      idDispID: if ExpectParentType(True) then
        begin
          Result.DispID := ParseIntExpr;
          Include(Result.PropAttr, ipaHasDispID);
        end;
      idReadOnly: if ExpectParentType(True) then
          Include(Result.PropAttr, ipaReadOnly);
      idWriteOnly: if ExpectParentType(True) then
          Include(Result.PropAttr, ipaWriteOnly);
      else
        ParseError('Invalid property directive: %s', [CurTokenString]);
    end;
  end;
  Expect(tkSemicolon);
  NextToken;
  if CurToken = tkIdentifier then
  begin
    // Only the Array property requires the default directive
    if SameText(CurTokenString, 'default') then
      Include(Result.PropAttr, ipaDefaultProp);
    NextToken;
    Expect(tkSemicolon);
    NextToken;
  end;
  if OldErr = FErrorCount then
    CheckProp(Result);
end;

function TParser.ParseLabeledStmt(const S: string): TStatement;
var
  Lab: TSymbol;
begin
  // todo 1: Consider the situation
  {
    if Value then
  L1:
      DoSome
    else
      DoOther;

    At this time, it cannot be analyzed normally
  }
  Lab := FindSymbol(FTemp);
  if Lab = nil then
    ParseError(SErr_UndeclaredIdent)
  else if Lab.NodeKind <> nkLabel then
    ParseError(SErr_LabelExpected)
  else if TStmtLabel(Lab).Stmt <> nil then
    ParseError(SErr_RedeclaredIdent);
  NextToken;
  if (Lab <> nil) and (Lab.NodeKind = nkLabel) then
  begin
    Result := TLabeledStmt(CreateStmt(TLabeledStmt));
    TStmtLabel(Lab).Stmt := TLabeledStmt(Result);
    TLabeledStmt(Result).LabelSym := TStmtLabel(Lab);
  end
  else
    Result := TEmptyStmt(CreateStmt(TEmptyStmt));
end;

procedure TParser.ParseLabelSection(Parent: TSymbol);
var
  Lab: TStmtLabel;
begin
  NextToken; // skip 'label'
  Lab := TStmtLabel(ParseIdList(TStmtLabel));
  while
    Lab <> nil do
  begin
    AddSymbol(Lab);
    Lab := TStmtLabel(Lab.Next);
  end;
  Expect(tkSemicolon);
  NextToken;
end;

function TParser.ParseLiteral: TExpr;
var
  V: TValueRec;
  I: int64;
  S: string;
begin
  ValInit(V);
  case CurToken of
    tkTrue, tkFalse: V := ValFromBool(CurToken = tkTrue);
    tkBinConst, tkOctalConst, tkIntConst, tkHexConst:
    begin
      I := FScanner.TokenValue.IntValue;
      if I <= $7FFFFFFF then
        ValFromInt(V, integer(I))
      else
        ValFromInt(V, I);
    end;
    tkStrConst, tkCharConst:
    begin
      S := CurTokenString;
      if Length(S) = 1 then
      begin
        ValFromChar(V, S[1]);
      end
      else
      begin
        if Self.FScanner.CurSourceFile.IsUtf8 then
          ValFromStr(V, S)
        else
          ValFromRawStr(V, S);
      end;
    end;
    else  // float
      ValFromReal(V, FScanner.TokenValue.RealValue);
  end;
  Result := CreateConstExpr(opCONST);
  TConstExpr(Result).Value := V;
  NextToken;
end;

function TParser.ParseMulExpr: TExpr;

  function MulOp(T: TToken): TExprOpCode;
  begin
    case T of
      tkMul: Result := opMUL;
      tkFDiv: Result := opFDIV;
      tkMod: Result := opMOD;
      tkDiv: Result := opIDIV;
      tkAnd: Result := opAND;
      tkSHR: Result := opSHR;
      tkSHL: Result := opSHL;
      else
        Result := opNONE;
    end;
  end;

var
  left, right: TExpr;
  op: TExprOpCode;
begin
{
<MulExpr>		::= <Factor>
			  | <MulExpr> <MulOp> <Factor>
}
  Result := ParseFactor;
  op := MulOp(CurToken);
  while op <> opNONE do
  begin
    NextToken;
    left := Result;
    right := ParseFactor;
    Result := CreateBinaryExpr(op, left, right);
    op := MulOp(CurToken);
  end;
end;

function TParser.ParseObjectType(const ObjName: string): TObjectType;
// todo 1: To be perfected
  procedure CheckObject(typ: TObjectType);
  var
    i: integer;
    sym: TSymbol;
  begin
    for i := 0 to typ.Symbols.Count - 1 do
    begin
      sym := typ.Symbols[i];
      case sym.NodeKind
        of
        nkMethod: if fmOverride in TMethod(Sym).Modifiers then  // Check if it's override;
            Include(TMethod(Sym).Modifiers, fmVirtual);
      end;
    end;
  end;

var
  Base: TSymbol;
  Field: TField;
  MethSym: TSymbol;
  Prop: TProperty;
  OldErr: integer;
  StateInfo: TParseStateInfo;
  OldParent: TSymbol;
  OldVis: TMemberVisibility;
  ClassPrefix, ClassVar: boolean;
begin
  Result := TObjectType(CreateElement(TObjectType));
  StateSet(psInObject, StateInfo);
  NextToken;  // skip 'object'
  if CurToken = tkBraceOpen then
  begin
    // parse base
    NextToken;
    Base := ParseQualifiedSym;
    if (Base.NodeKind <> nkType) or (TType(Base).TypeCode <> typObject) then
      ParseError(SErr_InvalidBaseObject)
    else
      Result.Base := TObjectType(Base);
    Expect(tkBraceClose);
    NextToken;
  end;
  Result.Name := ObjName;
  AddSymbol(Result);
  Result.GlobalAlignSize := FAlignSize;
  if psInPacked in FCurStates then
    Result.GlobalAlignSize := 1;
  OldErr := FErrorCount;
  OldVis := FCurVisibility;
  FCurVisibility := visPublic;
  ClassPrefix := False;
  ClassVar := False;
  EnterScope(Result.Symbols);
  OldParent := FCurParent;
  FCurParent := Result;
  while True do
    case CurToken of
      tkPrivate:
      begin
        FCurVisibility := visPrivate;
        NextToken;
      end;
      tkProtected:
      begin
        FCurVisibility := visProtected;
        NextToken;
      end;
      tkPublic:
      begin
        FCurVisibility :=
          visPublic;
        NextToken;
      end;
      tkPublished:
      begin
        FCurVisibility := visPublished;
        NextToken;
      end;
      tkStrict:
      begin
        NextToken;
        if CurToken = tkPrivate then
          FCurVisibility := visStrictPrivate
        else if CurToken = tkProtected then
          FCurVisibility := visStrictProtected
        else
          ParseError(SErr_ExpectProtectOrPrivate, True);
        NextToken;
      end;
      tkIdentifier:
      begin
        Field := ParseField(TField);
        while Field <> nil do
        begin
          Field.Visibility := FCurVisibility;
          if ClassVar then
            Include(Field.Attr, saStatic);
          AddSymbol(Field);
          Field := TField(Field.Next);
        end;
        Expect(tkSemicolon);
        NextToken;
      end;
      tkVar:
      begin
        NextToken;
        ClassVar := False;
      end;
      tkConst: Self.ParseConstSection(Result);
      tkType: Self.ParseTypeSection(Result);
      tkClass:
      begin
        ClassPrefix := True;
        NextToken;
        if CurToken = tkVar then
        begin
          ClassVar := True;
          NextToken;
        end
        else if not (CurToken in [tkFunction, tkProcedure, tkProperty]) then
          ParseError(SErr_ExpectMethodOrProperty, True);
      end;
      tkFunction, tkProcedure:
      begin
        MethSym := ParseFunction(Result);
        MethSym.Visibility := FCurVisibility;
        if MethSym.NodeKind <> nkMethod then
          ParseError(MethSym.Coord, 'Method required');
        if ClassPrefix then
          Include(MethSym.Attr, saClass);
        if fmStatic in TMethod(MethSym).Modifiers then
          Include(MethSym.Attr, saStatic);
        ClassPrefix := False;
        if (MethSym.NodeKind = nkMethod) and (TMethod(MethSym).ID > 0) then
          Result.Symbols.AddOvrld(TMethod(MethSym));
      end;
      tkProperty:
      begin
        Prop := ParseProperty(Result, ClassPrefix);
        Prop.Visibility := FCurVisibility;
        AddSymbol(Prop);
        if ClassPrefix then
          Include(Prop.Attr, saStatic);
      end;
      tkEnd: Break;
      else
        Expect(tkIdentifier);
    end;
  Expect(tkEnd);
  NextToken;
  Result.Hints := ParseHints;
  StateRestore(StateInfo);
  LeaveScope;
  FCurParent := OldParent;
  FCurVisibility := OldVis;
  // Check the Symbols
  if FErrorCount = OldErr then
    CheckObject(Result);
  if FErrorCount = OldErr then
    Result.Update(Self.FPointerSize);
end;

function TParser.ParseProgram: TModule;

  procedure SkipArgs;
  begin
    NextToken; // skip '('
    while
      True do
    begin
      Expect(tkIdentifier, True);
      NextToken;
      if CurToken <> tkComma then
        Break;
      NextToken;
    end;
    NextToken; // skip ')'
    Expect(tkSemicolon);
  end;

  procedure CleanupSym;   //   <====   HERE
  var
    st: TSymbolTable;
  begin
    st := FModule.InternalSymbols;
    FModule.InternalSymbols := FModule.Symbols;
    FModule.Symbols := st;
  end;

begin
{
<ProgHeader>		::= PROGRAM <RefId> <OptProgParamList> ';'
<OptProgParamList>	::= '(' <IdList> ')'
}
  NextToken; // skip 'program'
  Expect(tkIdentifier, True);
  FModule := TModule(CreateElement(TModule));
  FModule.Name := CurTokenString;
  FModule.Kind := mkProgram;
  FModule.TimeStamp := FScanner.TimeStamp;
  NextToken;
  if CurToken = tkBraceOpen then
    SkipArgs
  else
    Expect(tkSemicolon, True);
  NextToken; // skip ';'
  EnterScope(FModule.Symbols);
  FContext.LoadSystemUnit;
  FModule.Symbols.AutoAddToOwner := False;
  AddSymbols(FContext.FSystemUnit);
  FModule.Symbols.AutoAddToOwner := True;
  FModule.LoadedUnits.Add(FContext.FSystemUnit);
  FCurParent := FModule;
  //SetTempExpr(True);
  FInternalSection := True;
  FCurStates := [psInImplSect];
  if CurToken = tkUses then
    ParseUsesClause;
  ParseBlock(FModule);
  FCurParent := nil;
  LeaveScope;
  FCurStates := [];
  // Check that all declarations are implemented
  CheckForward;
  CleanupSym;
  Result := FModule;
end;

function TParser.ParseProperty(Parent: TType; IsStatic: boolean): TProperty;
// Check the validity of Expr, if it is invalid, return false, and the error message is sent through ParseError
// Returns true
  function IsMemberExpr(E: TExpr): boolean;
  var
    Elem: TSymbol;
  begin
    Result := False;
    if E.OpCode = opSYMBOL then
    begin
      Elem := TSymbolExpr(E).reference;
      if (Elem.NodeKind in [nkField, nkMethod]) then
      begin
        if Elem.Parent = Parent then
          Result := True
        else
          ParseError('%s must be a member of %s', [Elem.Name, Parent.Name]);
      end
      else
        ParseError('%s must be a field or method of %s', [Elem.Name, Parent.Name]);
      Exit;
    end;
    // It can be a field in a record, but it's not accessible by pointers
    while E <> nil do
    begin
      if E.OpCode = opMEMBER then
      begin
        if not (TBinaryExpr(E).Left.Typ.TypeCode in [typRecord, typObject]) then
        begin
          ParseError('Only record or object type allow in accessor expression');
          Exit;
        end
        else if TSymbolExpr(TBinaryExpr(E).Right).reference.NodeKind <> nkField then
        begin
          ParseError('Only field allow in accessor expression');
          Exit;
        end
        else
          E := TBinaryExpr(E).Left;
      end
      else if E.OpCode = opSYMBOL then
        Break
      else
        Exit;  // invalid operator
    end;
    Elem := TSymbolExpr(E).reference;
    if Elem.NodeKind <> nkField then
      ParseError('%s must be a field of %s', [Elem.Name, Parent.Name])
    else if Elem.Parent <> Parent then
      ParseError('%s must be a member of %s', [Elem.Name, Parent.Name])
    else
      Result := True;
  end;

  function GetAccessor(E: TExpr): TMultiAccessor;
  var
    R: TSymbolExpr;
  begin
    while E <> nil do
    begin
      if E.OpCode = opMEMBER then
        E := TBinaryExpr(E).Left
      else
        Break;
    end;
    Result := TMultiAccessor(CreateElement(TMultiAccessor));
    Result.Add(TField(TSymbolExpr(E).reference));
    E := E.Parent;
    while E <> nil do
    begin
      R := TSymbolExpr(TBinaryExpr(E).Right);
      Result.Add(R.reference);
      E := E.Parent;
    end;
  end;

  function ParseAccessor: TSymbol;
  var
    E: TExpr;
  begin
    // CurToken is tkIdentifier
    E := CreateSymbolExpr(CurTokenString);
    NextToken;
    while CurToken = tkDot do
    begin
      NextToken;
      Expect(tkIdentifier);
      E := CreateBinaryExpr(opMEMBER, E);
      TBinaryExpr(E).Right := CreateSymbolExpr(CurTokenString);
      NextToken;
    end;
    Include(FCurStates, psInAccessor);
    Result := nil;
    if CheckExpr(E) then
      if IsMemberExpr(E) then
      begin
        if E.OpCode = opSYMBOL then
          Result := TSymbolExpr(E).reference
        else
          Result := GetAccessor(E);
      end;
    Exclude(FCurStates, psInAccessor);
    ReleaseExpr(E);
  end;

  function ParseStoredProc: TSymbol;
  var
    E: TExpr;
  begin
    Result := nil;
    // todo 1: Constants may not be analyzed with Checkexpr here
    E := ParseConstExpr;
    if CheckExpr(E) then
    begin
      if not E.Typ.IsBoolean then
        ParseError('bool expression expected')
      else if IsMemberExpr(E) then
        Result := GetAccessor(E)
      else
      begin
        ValClear(FTempValue);
        TryEvalGet(E, FTempValue);
        if ValToBool(FTempValue) then
          Result := FContext.FTrueConst
        else
          Result := FContext.FFalseConst;
        ValClear(FTempValue);
      end;
    end;
  end;

  function IsSameType(t1, t2: TType): boolean;
  begin
    t1 := t1.OriginalType;
    t2 := t2.OriginalType;
    if t1.TypeCode = typSubrange then
      t1 := TSubrangeType(t1).BaseType;
    if t2.TypeCode = typSubrange then
      t2 := TSubrangeType(t2).BaseType;
    //  Result := t1 = t2;
    Result := t1.Equals(t2);
  end;

  function CheckPropStatic(Prop: TProperty; Elem: TSymbol): boolean;
  begin
    if saStatic in Prop.Attr then
      Result := saStatic in Elem.Attr
    else
      Result := not (saStatic in Elem.Attr);
    if Result then
      Exit;
    if saStatic in Prop.Attr then
      ParseError(Prop.Coord, 'Static property not allow non-static accessor')
    else
      ParseError(Prop.Coord, 'Non-static property not allow static accessor');
  end;

  procedure CheckGetterArgs(Prop: TProperty; MethodArgs: TFuncParamList);
  var
    I, ExpectArgCount: integer;
    A1, A2: TFuncParam;
  begin
    if Prop.HasIndexSpec then
      ExpectArgCount := 1
    else
      ExpectArgCount := Prop.ParamCount;
    if MethodArgs = nil then
    begin
      if ExpectArgCount <> 0 then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end
    else if Prop.HasIndexSpec then
    begin
      A1 := MethodArgs[0];
      if (not A1.ParamType.IsInt32) or (A1.Modifier in [argVar, argOut]) then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end
    else
      for
        I := 0 to Prop.ParamCount - 1 do
      begin
        A1 := Prop.Params[I];
        A2 := MethodArgs[I];
        if not IsSameType(A1.ParamType, A2.ParamType) or (A1.Modifier <> A2.Modifier) then
        begin
          ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
          Exit;
        end;
      end;
  end;

  procedure CheckGetter(Prop: TProperty);
  var
    OldErr: integer;
  begin
    if Prop.Getter = nil then
      Exit;
    OldErr := FErrorCount;
    case Prop.Getter.NodeKind of
      nkField:
      begin
        if not IsSameType(Prop.PropType, TField(Prop.Getter).FieldType) then
          ParseError(Prop.Coord, 'Accessor type not matched')
        else
          CheckPropStatic(Prop, TField(Prop.Getter));
      end;
      nkMethod:
      begin
        if not IsSameType(Prop.PropType, TMethod(Prop.Getter).ReturnType) then
          ParseError(Prop.Coord, 'Accessor type not matched')
        else
          CheckPropStatic(Prop, TMethod(Prop.Getter));
        if OldErr = FErrorCount then
          CheckGetterArgs(Prop, TMethod(Prop.Getter).Params);
      end;
      else
      begin
        if not IsSameType(Prop.PropType, TMultiAccessor(Prop.Getter).Last.FieldType) then
          ParseError(Prop.Coord, 'Accessor type not matched')
        else
          CheckPropStatic(Prop, TMultiAccessor(Prop.Getter).First);
      end;
    end;
  end;

  procedure CheckSetterArgs(Prop: TProperty; MethodArgs: TFuncParamList);
  var
    I, ExpectArgCount: integer;
    A1, A2: TFuncParam;
  begin
    if Prop.HasIndexSpec then
      ExpectArgCount := 2
    else
      ExpectArgCount := Prop.ParamCount + 1;
    if MethodArgs = nil then
    begin
      if ExpectArgCount <> 0 then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end
    else if Prop.HasIndexSpec then
    begin
      A1 := MethodArgs[0];
      A2 := MethodArgs[1];
      if (not A1.ParamType.IsInt32) or (A1.Modifier in [argVar, argOut]) then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched)
      else if not IsSameType(A2.ParamType, Prop.PropType) or (A2.Modifier in [argVar, argOut]) then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end
    else
    begin
      { Setter:
        procedure SetValue(i: Integer; value: Double);
      }
      for I := 0 to Prop.ParamCount - 1 do
      begin
        A1 := Prop.Params[I];
        A2 := MethodArgs[I];
        if not IsSameType(A1.ParamType, A2.ParamType) or (A1.Modifier <> A2.Modifier) then
        begin
          ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
          Exit;
        end;
      end;
      A1 := MethodArgs[MethodArgs.Count - 1];
      if not IsSameType(Prop.PropType, A1.ParamType) or (A1.Modifier in [argVar, argOut]) then
        ParseError(Prop.Coord, SErr_AccessorMethodArgsNotMatched);
    end;
  end;

  procedure CheckSetter(Prop: TProperty);
  var
    OldErr: integer;
  begin
    if Prop.Setter = nil then
      Exit;
    OldErr := FErrorCount;
    case Prop.Setter.NodeKind of
      nkField:
      begin
        if not IsSameType(Prop.PropType, TField(Prop.Setter).FieldType) then
          ParseError(Prop.Coord, 'Accessor type not matched')
        else
          CheckPropStatic(Prop, TField(Prop.Setter));
      end;
      nkMethod:
      begin
        if TMethod(Prop.Setter).ReturnType <> nil then
          ParseError(Prop.Coord, 'Setter method not allow return value')
        else
          CheckPropStatic(Prop, TMethod(Prop.Setter));
        if OldErr = FErrorCount then
          CheckSetterArgs(Prop, TMethod(Prop.Setter).Params);
      end;
      else
      begin
        if not IsSameType(Prop.PropType, TMultiAccessor(Prop.Setter).Last.FieldType) then
          ParseError(Prop.Coord, 'Accessor type not matched')
        else
          CheckPropStatic(Prop, TMultiAccessor(Prop.Setter).First);
      end;
    end;
  end;

  procedure CheckStored(Prop: TProperty);
  var
    Meth: TMethod;
  begin
    if Prop.Stored = nil then
      Exit;
    case
      Prop.Stored.NodeKind of
      nkMethod:
      begin
        Meth := TMethod(Prop.Stored);
        if not (Meth.ParamCount = 1) or not (TFuncParam(Meth.Params[0]).ParamType.IsInt32) then
          ParseError(Prop.Coord, 'Accessor arguments not matched');
      end;
    end;
  end;

  procedure CheckProp(Prop: TProperty);   //   <====   HERE
  var
    OldErr: integer;
  begin
    // 1. Check the type
    // 2. Check the parameters
    // 3. There is an index, the Accessor cannot be a field, and the attribute cannot be an Array
    // 4. The Accessor of class property must be class var or class method
    // 5. Getter and setter must have a non-nil
    // 6.Array property can have default

    // todo 2: getter/setter/stored requires ccDefault

    if Prop.HasIndexSpec and (Prop.ParamCount > 0) then
      ParseError(Prop.Coord, 'Array property not allow index directive')
    else if (saStatic in Prop.Attr) and (Prop.Stored <> nil) then
      ParseError(Prop.Coord, 'Class property not allow stored directive')
    else if (Prop.Getter = nil) and (Prop.Setter = nil) then
      ParseError(Prop.Coord, 'Getter and Setter not allow be also nil')
    else if (paDefaultProp in Prop.PropAttr) and (Prop.ParamCount = 0) then
      ParseError(Prop.Coord, 'Non-array property not allow default directive')
    else
    begin
      OldErr := FErrorCount;
      CheckGetter(Prop);
      if OldErr = FErrorCount then
        CheckSetter(Prop);
      if OldErr = FErrorCount then
        CheckStored(Prop);
    end;
  end;

  procedure FindBaseDecl(Prop: TProperty);
  var
    Elem: TSymbol;
    BaseProp: TProperty;
  begin
    case Parent.TypeCode of
      typClass: Elem := TClassType(Parent).FindBaseSymbol(Prop.Name);
      typObject: Elem := TObjectType(Parent).FindBaseSymbol(Prop.Name);
      else
        Elem := nil;
    end;
    if (Elem = nil) or (Elem.NodeKind <> nkProperty) then
      ParseError(Prop.Coord, 'Property %s not exists in base', [Prop.Name])
    else
    begin
      BaseProp := TProperty(Elem);
      if (saStatic in BaseProp.Attr) xor (saStatic in Prop.Attr) then
      begin
        ParseError(Prop.Coord, 'Property %s different from base', [Prop.Name]);
        Exit;
      end;
      if Prop.PropType = nil then
        Prop.PropType := BaseProp.PropType;
      if Prop.Getter = nil then
        Prop.Getter := BaseProp.Getter;
      if Prop.Setter = nil then
        Prop.Setter := BaseProp.Setter;
      if Prop.Stored = nil then
        Prop.Stored := BaseProp.Stored;
      if not Prop.HasIndexSpec then
        Prop.Index := BaseProp.Index;
      if ValIsClear(Prop.DefaultValue) and not ValIsClear(BaseProp.DefaultValue) then
        ValCopy(Prop.DefaultValue, BaseProp.DefaultValue);
    end;
  end;

var
  FullDecl: boolean;
  PropD: TPropDirective;
  OldErr: integer;
begin
  {
  <PropertySpec>		::= PROPERTY <PropertyDecl> <OptPropSpecifiers> ';'

  <PropertyDecl>		::= <RefId>                     ':' <TypeRef>
  			  | <RefId> '[' <IndexList> ']' ':' <TypeRef>
  			  | <RefId>
  }
  NextToken;
  Expect(tkIdentifier);
  Result := TProperty(CreateElement(TProperty));
  Result.Name := CurTokenString;
  NextToken;
  FullDecl := False;
  if CurToken = tkSquaredBraceOpen then
  begin
    //    NextToken;
        // parse array property args
    Result.CreateParams;
    Self.ParseFuncParamList(Result, Result.Params);
    Expect(tkColon);
    FullDecl := True;
  end;
  if CurToken = tkColon then
  begin
    NextToken;
    Result.PropType := ParseTypeRef;
    FullDecl := True;
  end;
  OldErr := Self.ErrorCount;
  while CurToken = tkIdentifier do
  begin
    // todo 5: This is where you can optimize. Added an option to consider Read and the like as keywords in Scanner
    PropD := ParsePropDirective(CurTokenString);
    NextToken;
    case PropD of
      idRead: Result.Getter := ParseAccessor;
      idWrite: Result.Setter := ParseAccessor;
      idIndex: Result.Index := ParseIntExpr;
      idStored: Result.Stored := ParseStoredProc;
      idNoDefault: Include(
          Result.PropAttr, paNoDefault);
      else
        ParseError('Invalid property directive: %s', [CurTokenString]);
    end;
  end;
  Expect(tkSemicolon);
  NextToken;
  if CurToken = tkIdentifier then  // Only the Array property requires the default directive
    if SameText(CurTokenString, 'default') then
    begin
      Include(Result.PropAttr, paDefaultProp);
      NextToken;
      Expect(tkSemicolon);
      NextToken;
    end;
  if IsStatic then
  begin
    Include(Result.Attr, saStatic);
    Include(Result.Attr, saClass);
  end;
  if not FullDecl then  // It's not a complete declaration, and you need to look up the base class declaration to refine it
    FindBaseDecl(Result);
  // If an error has already occurred above, you don't need to check
  if OldErr = Self.ErrorCount then
    CheckProp(Result);
end;

procedure TParser.ParseQualifiedId(const First: string);
begin
  if First = '' then
  begin
    Expect(tkIdentifier);
    FQId.Name := CurTokenString;
    NextToken;
  end
  else
    FQId.Name := First;
  FQId.CountOfNames := 1;
  while CurToken = tkDot do  // System.SysUtils.Id This is the case
  begin
    // Allow reserved words to appear in tkDot(.) afterwards
    // For example, MyUnit.Type
    Scanner.NoReservedWord := True;
    NextToken;
    Scanner.NoReservedWord := False;
    Expect(tkIdentifier);
    if FQId.CountOfNames > Length(FQId.Names) then
      SetLength(FQId.Names, Length(FQId.Names) + 10);
    FQId.Names[FQId.CountOfNames] := CurTokenString;
    NextToken;
    Inc(FQId.CountOfNames);
  end;
  FQId.Names[0] := FQId.Name;
end;

function TParser.ParseQualifiedSym(const First: string): TSymbol;   //   <====   HERE
var
  Sym: TSymbol;
  I: integer;
begin
  ParseQualifiedID(First);
  if FQId.CountOfNames = 1 then
    Result := FindSymbol(FQId.Name)
  else
  begin
    Sym := FindSymbol(FQId.Name);
    for I := 1 to FQID.CountOfNames - 1 do
    begin
      if not Assigned(Sym) then
        Break;
      case Sym.NodeKind of
        nkModule: Sym := TModule(Sym).FindSymbol(FQId.Names[I]);
        nkNameScope: Sym := TNameScope(Sym).FindSymbol(FQId.Names[I]);
        nkType: case TType(Sym).TypeCode of
            typClass: Sym := TClassType(Sym).FindSymbol(FQId.Names[I]);
            typRecord: Sym := TRecordType(Sym).FindSymbol(FQId.Names[I]);
            typObject: Sym := TObjectType(Sym).FindSymbol(FQId.Names[I]);
            else
              Sym := nil;
          end;
        else
          Sym := nil;
      end;
      if Sym = nil then
        Break;
      if not IsVisible(FCurParent, Sym) then
        ParseError(SErr_SymbolNotAccess, [Sym.Name]);
    end;
    Result := Sym;
  end;
end;

function TParser.ParseRaiseStmt: TRaiseStmt;
begin
  // raise object_expression
  // raise object_expression at pointer_expression
  Result := TRaiseStmt(CreateStmt(TRaiseStmt));
  NextToken; // skip 'raise'
  if (CurToken in [tkSemicolon, tkEnd, tkElse]) then
    Exit;
  Result.Expr := Self.ParseDesignator;
  if CheckExpr(Result.Expr) then
    if Result.Expr.Typ.TypeCode <> typClass then
      ParseError(Result.Expr.Coord, SErr_ClassRequired);
end;

function TParser.ParseRecordType(const TypName: string; Parent: TSymbol): TRecordType;

  procedure CheckSelector(E: TExpr; T: TType);
  begin
  end;

  function ParseRecordBody(BodyClass: TRecordBodyClass; var Body: TRecordBody): TRecordBody;
  var
    Field: TField;
    B1, B2: TRecordVariant;
    E: TExpr;
  begin
    Result := BodyClass.Create;
    Body := Result;
    B2 := nil;
    while (CurToken <> tkEnd) and (CurToken <> tkBraceClose) do
    begin
      if CurToken = tkCase then
      begin
        NextToken; // skip 'case'
        Expect(tkIdentifier);
        FTemp := CurTokenString;
        Result.Selector := TField(CreateElement(TField));
        NextToken;
        if CurToken = tkColon then
        begin
          // TODO: 2 This part has not been tested yet
          // The previous one was the Selector Field Name
          Result.Selector.Name := FTemp;
          FTemp := '';
          NextToken;
        end
        else
          UngetToken;
        Result.
          Selector.FieldType := ParseTypeRef;
        Expect(tkOf);
        NextToken;
        if Result.Selector.Name <> '' then
          AddSymbol(Result.Selector);
        B1 := nil;
        repeat
          E := ParseExprList;
          // todo 5: Need to check for E-type compatibility
          CheckSelector(E, Result.Selector.FieldType);
          ReleaseExpr(E);
          Expect(tkColon);
          NextToken;
          Expect(tkBraceOpen);
          NextToken;
          //B2 := TRecordVariant(ParseRecordBody(TRecordVariant));
          ParseRecordBody(TRecordVariant, TRecordBody(B2));
          if Result.Variants = nil then
            Result.Variants := B2;
          if B1 <> nil then
            B1.Next := B2;
          B1 := B2;
          Expect(tkBraceClose);
          NextToken;
          if CurToken = tkSemiColon then
            NextToken
          else
            Break;
          if (CurToken = tkEnd) or (CurToken = tkBraceClose) then
            Break;
        until False;
      end
      else
      begin
        Field := TField(ParseField(TField));
        while Field <> nil do
        begin
          Field.Visibility := visPublic;
          AddSymbol(Field);
          if Result.ClassType = TRecordVariant then
            Include(Field.FieldAttr, faRecVar);
          Result.
            Members.Add(Field);
          Field := TField(Field.Next);
        end;
        if CurToken = tkSemicolon then
          NextToken;
      end;
    end;
  end;

var
  OldParent: TSymbol;
begin
  NextToken; // skip 'record'
  Result := TRecordType(CreateElement(TRecordType));
  Result.Name := TypName;
  if Result.Name <> '' then
  begin
    AddSymbol(Result);
  end;
  EnterScope(Result.Symbols);
  OldParent := FCurParent;
  FCurParent := Parent;
  //Result.Body :=
  ParseRecordBody(TRecordBody, Result.Body);
  Expect(tkEnd);
  NextToken;
  if not (psInVar in Self.FCurStates) then
    Result.Hints := ParseHints;
  FCurParent := OldParent;
  LeaveScope;
  Result.GlobalAlignSize := FAlignSize;
  if psInPacked in FCurStates then
    Result.GlobalAlignSize := 1;
  Result.Update;
  {  if Result.Size > $7fffffff then
      ParseError(Result.Coord, 'Type size may be exceed than 2GB');}
end;

function TParser.ParseRepeatStmt: TRepeatStmt;
var
  StateInfo: TParseStateInfo;
begin
  NextToken; // skip 'repeat'
  StateSet(psInWhileStmt, StateInfo);
  Result := TRepeatStmt(CreateStmt(TRepeatStmt));
  Result.Stmt := ParseStmtList(Result, [tkUntil]);
  StateRestore(StateInfo);
  Expect(tkUntil);
  NextToken;
  Result.Condition := ParseExpr;
  CheckBoolExpr(Result.Condition);
  //  Expect(tkDo);
  //  NextToken;
  //  Result.Stmt := ParseStatement(Result);
end;

procedure TParser.ParseResStringSection(Parent: TSymbol);
var
  V: TConstant;
begin
  NextToken; // skip 'resourcestring'
  Expect(tkIdentifier);
  repeat
    V := TConstant(CreateElement(TConstant));
    V.Name := CurTokenString;
    NextToken;
    Expect(tkEqual);
    NextToken;
    V.Value := ValFromStr(ParseStrExpr('1'));
    V.Visibility := FCurVisibility;
    V.IsResStr := True;
    Expect(tkSemicolon);
    AddSymbol(V);
    NextToken;
  until
    CurToken <> tkIdentifier;
end;

function TParser.ParseSetConstructor: TExpr;
begin
  Expect(tkSquaredBraceOpen);
  Result := CreateUnaryExpr(opSET);
  NextToken;
  if CurToken <> tkSquaredBraceClose then
    TUnaryExpr(Result).Operand := ParseSetElementList
  else
    TUnaryExpr(Result).Operand := CreateListExpr;
  Expect(tkSquaredBraceClose);
  NextToken;
end;

function TParser.ParseSetElementList: TExpr;

  function ParseSetElement: TExpr;
  var
    L: TExpr;
  begin
    Result := ParseExpr;
    if CurToken = tkDotDot then
    begin
      L := Result;
      Result := CreateBinaryExpr(opRANGE);
      TBinaryExpr(Result).Left := L;
      NextToken;
      TBinaryExpr(Result).Right := ParseExpr;
    end;
  end;

var
  L: TExpr;
begin
  // To read the SET expression list, the number must be >=1
  Result := CreateListExpr;
  L := ParseSetElement;
  TListExpr(Result).Add(L);
  while CurToken = tkComma do
  begin
    NextToken;
    L := ParseSetElement;
    TListExpr(Result).Add(L);
  end;
end;

function TParser.ParseSimpleStmt: TStatement;

  function SymbolCanAssignTo(Ref: TSymbol): boolean;
  begin
    case Ref.NodeKind of
      nkVariable: Result := not (vaReadOnly in TVariable(Ref).VarAttr);
      nkField: Result := True;
      nkProperty: Result := TProperty(Ref).Setter <> nil;
      nkIntfProperty: Result := TIntfProperty(Ref).Setter <> nil;
      nkFuncParam: Result := TFuncParam(Ref).Modifier <> argConst;
      else
        Result := False;
    end;
  end;

  function PropAssign(L, R: TExpr): TStatement;
  var
    Ref: TSymbol;
    Setter: TSymbol;
    New: TExpr;
    Args: TExpr;
    S: TCallStmt;
  begin
    Result := nil;
    if (L.OpCode = opMEMBER) or (eaArrayProp in L.Attr) then
    begin
      if eaArrayProp in L.Attr then
      begin
        Assert(L.OpCode = opINDEX);
        Args := TBinaryExpr(L).Right;
        L := TBinaryExpr(L).Left;
      end
      else
        Args := nil;
      Ref := L.GetReference;
      case Ref.NodeKind of
        nkProperty: Setter := TProperty(Ref).Setter;
        nkIntfProperty: Setter := TIntfProperty(Ref).Setter;
        else
          Setter := nil;
      end;
      if (Setter <> nil) and (Setter.NodeKind = nkMethod) then
      begin
        New := CreateBinaryExpr(opCALL, L, nil);
        New.Coord := L.Coord;
        if Args = nil then
        begin
          Args := CreateListExpr;
          Args.Coord := L.Coord;
          Args.Typ := FContext.FUntype;
        end;
        Assert(Args.OpCode = opLIST);
        TListExpr(Args).Add(R);
        TBinaryExpr(New).Right := Args;
        S := TCallStmt(CreateStmt(TCallStmt));
        S.Coord := New.Coord;
        S.CallExpr := New;
        Result := S;
      end;
    end;
  end;

  // Check if it can be used as an lvalue
  function CheckLValue(L: TExpr): boolean;

    function IsSizeEqual(E: TExpr): boolean;
    var
      Left, R: TExpr;
    begin
      // Check when the lvalue is a Cast:
      // Integer(P^) := 4;
      // Word(pWide^) := 0;

      // E is TBinaryExpr with opCAST
      // E.Right is opLIST
      R := TBinaryExpr(E).Right;
      Left := TBinaryExpr(E).Left;
      if R.Typ.TypeCode = typUntype then
        Result := True
      else
        Result := Left.Typ.Size = R.Typ.Size;
    end;

  var
    Ref: TSymbol;
  begin
    // Must point to a memory address
    {
      var p: pchar;
      p := nil;
      p^ := a;
      (p + 1)^ := #0;
      @procvar := nil;
      arr[5] := 1;
      Integer(p^) := 5;
    }
    case L.OpCode of
      opMEMBER:
      begin
        Ref := TSymbolExpr(TBinaryExpr(L).Right).reference;
        Result := SymbolCanAssignTo(Ref);
      end;
      opSYMBOL:
      begin
        Ref := TSymbolExpr(L).reference;
        Result := SymbolCanAssignTo(Ref);
      end;
      opINDEX: Result := True;  // todo 1: There's a problem here, array property
      { case:
        Item[0][1] := 'd'; // Item[0] return TStrings, pchar, this ok
        Item[0][1] := 'd'; // Item[0] return string, this not ok
        p^[1] := 'd';      // p^ is tstrings, pchar, etc. this ok
        arrprop[1] := 'd'; // arrprop is readonly property, this not ok
      }
      { opINDEX: begin
        if TBinaryExpr(L).Left.OpCode = opMEMBER then
        begin
          Ref := TBinaryExpr(L).Left.GetReference;
          Result := SymbolCanAssignTo(Ref);
        end else
          Result := True;
      end;}
      opINST: Result := L.Typ.TypeCode <> typUntype;
      opCAST: Result := IsSizeEqual(L);   // todo 2: Probably not required
      opADDR: Result := TUnaryExpr(L).Operand.Typ.TypeCode = typProcedural;
      else
        Result :=
          False;
    end;
  end;

  function CheckLExpr(var L: TExpr): boolean;
  begin
    Include(FCurStates, psInLeftVal);
    Result := CheckExpr(L);
    Exclude(FCurStates, psInLeftVal);
  end;

  function CheckRExpr(L: TExpr; var R: TExpr): boolean;
  begin
    // Handled: Assign a function to a function variable
    FExpectedProcType := L.Typ.TypeCode = typProcedural;
    Result := CheckExpr(R);
    FExpectedProcType := False;
  end;

  procedure CheckAssign(L, R: TExpr);
  begin
    if not CanAssign(L.Typ, R) then
      ParseError(L.Coord, SErr_IncompatibleTypes);
{   if (L.Typ.TypeCode = typClassRef) and (R.Typ.TypeCode = typClass) then
      if not R.IsTypeSymbol then
      begin
        ParseError(L.Coord, SErr_IncompatibleTypes);
        Exit;
      end;

    if R.IsNilConst and (L.Typ.TypeCode in [typPointer, typClass,
        typClassRef, typPAnsiChar, typPWideChar, typDynamicArray,
        typInterface]) then
    begin
      Exit;
    end;

    // case: R is string constant, L is PAnsiChar,PWideChar,PackedString
    if R.IsStringConstant and (L.Typ.IsStringArithCompatible) then
      Exit;

    if not CheckAssignCompatibility(L.Typ, R.Typ) then
      ParseError(L.Coord, SErr_IncompatibleTypes);}
  end;

  procedure ProcessDelayed(L, R: TExpr);
  begin
    // Case: p:= @proc; proc is an overloaded function, and CheckExpr cannot determine which overload is required for proc
    if R.OpCode <> opADDR then
      InternalError('Expect opADDR in ProcessDelayed');
    if R.Typ.TypeCode <> typProcedural then
      InternalError('Expect procedural type in ProcessDelayed');
    // The overloaded function can be assigned to the Pointer type, taking the first function
    if L.Typ.IsUntypePointer then
      Exit;
    if L.Typ.TypeCode <> typProcedural then
      ParseError(L.Coord, SErr_IncompatibleTypes);
    FindProper(TUnaryExpr(R), TProceduralType(L.Typ));
    Exclude(R.Attr, eaDelayed);
  end;

var
  L, R: TExpr;
//  AsgStmt: TAssignmentStmt;
begin
  if CurToken in [tkIdentifier, tkIntConst, tkAt, tkInherited] then
  begin
    FTemp := CurTokenString;
    NextToken;
    if CurToken = tkColon then
    begin  // (tr. (grade?) (label?)
      Result := ParseLabeledStmt(FTemp);
      FTemp := '';
    end
    else
    begin
      UngetToken;
      if CurToken = tkAt then
        L := ParseFactor
      else
        L := ParseDesignator;
      // / In this case: @proc := GetProcAddress
      if L.OpCode = opADDR then
        Expect(tkAssign);
      Result := nil;
      if CurToken = tkAssign then
      begin
        NextToken;
        {AsgStmt := TAssignmentStmt(CreateStmt(TAssignmentStmt));
        Result := AsgStmt;
        AsgStmt.Left := L;
        AsgStmt.Right := ParseExpr;}
        R := ParseExpr;
        if CheckLExpr(L) and CheckRExpr(L, R) then
        begin
          if not CheckLValue(L) then
            ParseError(L.Coord, SErr_NotAssign);
          // Check the rvalue
          if R.Typ.TypeCode = typUntype then
            ParseError(SErr_ExprNoValue)
          else
          begin
            if eaDelayed in R.Attr then
              ProcessDelayed(L, R);
            CheckAssign(L, R);
          end;
          Result := PropAssign(L, R);
        end;
        if not Assigned(Result) then
        begin
          Result := CreateStmt(TAssignmentStmt);
          Result.Coord := L.Coord;
          TAssignmentStmt(Result).Left := L;
          TAssignmentStmt(Result).Right := R;
        end;
      end
      else
      begin
        // call stmt
        Result := CreateStmt(TCallStmt);
        if CheckExpr(L) then
          if not (L.OpCode in [opCALL]) then
            // todo 1: (seems to have been solved) There is a problem with obj.show and the like
            ParseError('Call statement expected');
        TCallStmt(Result).CallExpr := L;
      end;
    end;
  end
  else
  begin
    ParseError(SErr_ExpectIdentifier);
    Result := CreateStmt(TCallStmt);
    NextToken;
  end;
end;

function TParser.ParseStatement(Parent: TStatement): TStatement;
label
  Start;
begin
  Start:
  // SetTempExpr(False);
    case CurToken of
      tkAsm:
      begin
        ParseError('Asm statement unsupported', True);
        Result := nil;
      end;
      tkIf: Result := ParseIfStmt;
      tkCase: Result := ParseCaseStmt;
      tkWhile: Result := ParseWhileStmt;
      tkFor: Result := ParseForStmt;
      tkRepeat: Result := ParseRepeatStmt;
      tkTry: Result := ParseTryStmt;
      tkWith: Result := ParseWithStmt(Parent);
      tkRaise: Result := ParseRaiseStmt;
      tkGoto: Result := ParseGotoStmt;
      tkBegin: Result := ParseCompoundStmt;
      tkElse: Result := nil;
      tkEnd: Result := nil;
      //    tkOn: Expect(tkIdentifier);
      tkSemicolon:
      begin
        while
        CurToken = tkSemicolon do
          NextToken;
        Result := nil;
        //Goto Start;
      end;
      else
        Result := ParseSimpleStmt;
    end;
  if Result <> nil then
    Result.Parent := Parent;
  // SetTempExpr(True);
end;

function TParser.ParseStmtList(Parent: TStatement; EndTokens: TTokens): TCompoundStmt;
var
  Stmt: TStatement;
begin
  // Similar to ParseCompoundStmt, but without begin and end.
  Result := TCompoundStmt(CreateStmt(TCompoundStmt));
  Result.Parent := Parent;
  while not (CurToken in EndTokens) do
  begin
    Stmt := ParseStatement(Result);
    if Stmt <> nil then
      Result.Statements.Add(Stmt);
    if CurToken = tkSemicolon then
      NextToken;
  end;
end;

function TParser.ParseStrExpr(const DefValue: string): string;
var
  E: TExpr;
begin
  E := ParseConstExpr;
  if CheckConstExpr(E) and (E.Typ.TypeCode = typString) then
  begin
    ValClear(FTempValue);
    if TryEvalGet(E, FTempValue) then
      Result := ValToStr(FTempValue)
    else
      Result := DefValue;
    ValClear(FTempValue);
  end
  else
  begin
    ParseError('String constant expression expected');
    Result := DefValue;
  end;
end;

function TParser.ParseTryStmt: TTryStmt;

  function IsOn: boolean;
  begin
    Result := (CurToken = tkOn) or ((CurToken = tkIdentifier) and SameText(CurTokenString, 'on'));
  end;

  function ParseExceptBlock(TryStmt: TTryStmt): TExceptBlock;
  var
    Handler: TExceptHandler;
    Sym: TSymbol;
  begin
    NextToken;   // skip 'except'
    Result := TExceptBlock.Create;
    TryStmt.ExceptBlock := Result;
    if IsOn then
    begin
      while True do
      begin
        if IsOn then
        begin
          NextToken;   // skip 'on'
          Handler := TExceptHandler.Create;
          Handler.ExceptVar := TVariable(CreateElement(TVariable));
          Result.AddExceptHandler(Handler);
          // parse except var
          Expect(tkIdentifier);
          FTemp := CurTokenString;
          NextToken;
          if CurToken = tkColon then
          begin
            // case 1, on E: Exception do
            NextToken; // skip ':'
            Handler.ExceptVar.Name := FTemp;
            FTemp := '';
          end;
          Include(Handler.ExceptVar.VarAttr, vaLocal);
          // case 2, on Exception do
          Sym := ParseQualifiedSym(FTemp);
          if Sym = nil then
            ParseError(SErr_UndeclaredIdent, [FQID.Id]);
          if (Sym.NodeKind <> nkType) and (TType(Sym).TypeCode <> typClass) then
          begin
            ParseError(SErr_ClassRequired);
            Sym := FContext.FTObjectType;
          end;
          FQID.Reset;
          Handler.ExceptVar.VarType := TType(Sym);
          Expect(tkDo);
          NextToken;
          if Handler.ExceptVar.Name <> '' then
            Self.CurSymbols.Add(Handler.ExceptVar);
          Handler.Stmt := Self.ParseStatement(TryStmt);
          if Handler.ExceptVar.Name <> '' then
            Self.CurSymbols.Remove(Handler.ExceptVar.Name);
          if CurToken = tkSemicolon then
            NextToken;
//          while CurToken = tkSemicolon do
//            NextToken;
        end
        else if CurToken = tkElse then
        begin
          NextToken;
          Result.Default := Self.ParseStmtList(TryStmt, [tkEnd]);
          Break;
        end
        else
          Break;
      end;
    end
    else // case 3, try dosome; except end;
      Result.Default := ParseStmtList(TryStmt, [tkEnd]);
  end;

begin
  NextToken; // skip 'try'
  Result := TTryStmt(CreateStmt(TTryStmt));
  Result.Stmt := ParseStmtList(Result, [tkFinally, tkExcept]);
  if CurToken = tkFinally then
  begin
    NextToken;
    Result.FinallyStmt := ParseStmtList(Result, [tkEnd]);
  end
  else
    ParseExceptBlock(Result);
  Expect(tkEnd);
  NextToken;
end;

function TParser.ParseTypeDecl(const TypName: string; Parent: TSymbol): TType;

  procedure ParseEnumType(T: TEnumType);
  var
    E: TEnumValue;
    Expr: TExpr;
    Value: integer;
  begin
    Value :=
      0;
    E := nil;
    //  SetTempExpr(True);
    NextToken; // skip '('
    repeat
      Expect(tkIdentifier);
      if CurToken = tkIdentifier then
      begin
        E := TEnumValue(CreateElement(TEnumValue));
        E.Name := CurTokenString;
        E.Value := Value;
        E.
          EnumType := T;
        T.Values.Add(E);
        AddSymbol(E);
      end
      else
        Break;
      NextToken;
      if CurToken = tkEqual then
      begin
        NextToken;
        ValClear(FTempValue);
        Expr := ParseConstExpr;
        if TryEvalGet(Expr, FTempValue) then
        begin
          Value := ValToInt(FTempValue);
          E.Value := Value;
        end;
        ValClear(FTempValue);
        ReleaseExpr(Expr);
      end
      else if CurToken <> tkComma then
        Break;
      Inc(Value);
      Expect(tkComma);
      NextToken;
    until False;
    //   ClearTempExprList;
    Expect(tkBraceClose);
    NextToken;
  end;

  function ParseTypeName(Alias: boolean): TType;
  var
    T: TType;
  begin
    Result := ParseTypeRef;
    if Result = FContext.FAnytype then
      ParseError('Type expected');
    if Alias then
    begin
      T := CreateType(TClonedAliasType);
      TClonedAliasType(T).RefType := Result;
      Result := T;
    end;
  end;

  function CanDelayDecl(Qd: TQualifiedId): boolean;
  begin
    // Without any qualification, the declaration can be deferred
    Result := Qd.CountOfNames = 1;
  end;

  function ParsePointerType: TType;
  var
    Typ: TType;
    Sym: TSymbol;
  begin
    sym := ParseQualifiedSym;
    if Sym = nil then
    begin
      if CanDelayDecl(FQId) then
      begin
        Typ := TUnresolvedType.Create;
        Typ.Name := FQID.Name;
      end
      else
      begin
        ParseError(SErr_UndeclaredIdent, [FQId.Id]);
        Typ := FContext.FIntegerType;
      end;
    end
    else if Sym.NodeKind <> nkType then
    begin
      ParseError(SErr_SymbolNotType, [FQId.Id]);
      Typ := FContext.FIntegerType;
    end
    else
      Typ := TType(Sym);
    FQId.Reset;
    Result := CreateType(TPointerType);
    TPointerType(Result).RefType := Typ;
    Result.Size := FPointerSize;
  end;

  function CheckSubRng(L, R: TExpr): boolean;
  var
    Sym: TSymbol;
  begin
    Result := False;
    if not L.Typ.IsOrdinal then
    begin
      ParseError(SErr_ExpectOrdinal);
      Exit;
    end;
    if not R.Typ.IsOrdinal then
    begin
      ParseError(SErr_ExpectOrdinal);
      Exit;
    end;
    Sym := L.GetReference;
    if (Sym <> nil) and not (Sym.NodeKind in [nkConstant, nkEnumElement]) then
    begin
      ParseError(SErr_ExpectOrdinal);
      Exit;
    end;
    Sym := R.GetReference;
    if (Sym <> nil) and not (Sym.NodeKind in [nkConstant, nkEnumElement]) then
    begin
      ParseError(SErr_ExpectOrdinal);
      Exit;
    end;
    Result := True;
  end;

  // Analyze two scenarios:
  // MyT = Vcl.TRect;
  // MyT = 1+2..5*6;
  function ParseType(Alias: boolean): TType;
  var
    L, R: TExpr;
    LVal, RVal: TValueRec;
  begin
    // todo 1: Note if ttt = aa.bb is supported
    R := nil;
    L := ParseTypeExpr;
    if CurToken = tkDotDot then
    begin
      NextToken;
      R := ParseTypeExpr;
      if CheckConstExpr(L) and CheckConstExpr(R) and CheckSubRng(L, R) then
      begin
        ValInit(LVal);
        ValInit(RVal);
        TryEvalGet(L, LVal);
        TryEvalGet(R, RVal);
        Result := CreateType(TSubrangeType);
        if ValToInt64(LVal) > ValToInt64(RVal) then
        begin
          TSubrangeType(Result).RangeBegin := ValToInt64(RVal);
          TSubrangeType(Result).RangeEnd := ValToInt64(LVal);
          ParseError(L.Coord, SErr_SubrangeOutOfBound);
        end
        else
        begin
          TSubrangeType(Result).RangeBegin := ValToInt64(LVal);
          TSubrangeType(Result).RangeEnd := ValToInt64(RVal);
        end;
        case L.Typ.TypeCode of
          typBool: TSubrangeType(Result).BaseType := FContext.FBooleanType;
          typChar: if TCharType(L.Typ).Kind = charAnsi then
              TSubrangeType(Result).BaseType := FContext.FAnsiCharType
            else
              TSubrangeType(Result).BaseType := FContext.FWideCharType;
          typEnum: TSubrangeType(Result).BaseType := L.Typ;
          else
            TSubrangeType(Result).BaseType :=
              FContext.TypeOfRange(TSubrangeType(Result).RangeBegin, TSubrangeType(Result).RangeEnd);
        end;
      end
      else
        Result := nil;
    end
    else if L.OpCode in [opSYMBOL, opMEMBER] then
    begin
      if CheckExpr(L) then
        Result := L.Typ
      else
        Result := nil;
    end
    else
    begin
      Result := nil;
      ParseError('Error in type declaration');
    end;
    ReleaseExpr(L);
    if R <> nil then
      ReleaseExpr(R);
  end;

{
<CallType> ::= PROCEDURE <OptFormalParms> <OptCallConventions>
      | PROCEDURE   <OptFormalParms>                  OF OBJECT <OptCallConventions>
      | FUNCTION    <OptFormalParms> ':' <ResultType>           <OptCallConventions>
      | FUNCTION    <OptFormalParms> ':' <ResultType> OF OBJECT <OptCallConventions>
}
  function ParseProceduralType: TProceduralType;

    function EndOfDecl: boolean;
    begin
      if psInVar in fCurStates then
        Result := (CurToken = tkEqual) or (CurToken = tkSemicolon)
      else
        Result := CurToken = tkSemicolon;
    end;

  var
    IsFunc: boolean;
    CC: TCallingConvention;
    M: TFunctionModifier;
  begin
    IsFunc := CurToken = tkFunction;
    NextToken; // skip 'function'/'procedure'
    Result := TProceduralType(CreateType(TProceduralType));
    if CurToken = tkBraceOpen then
    begin
      Result.CreateParams;
      ParseFuncParamList(Result, Result.Params);
    end;
    if IsFunc then
    begin
      // parse return type
      Expect(tkColon);
      if CurToken = tkColon then
        NextToken;
      Result.ReturnType :=
        ParseTypeRef;
    end;
    if CurToken = tkOf then
    begin
      NextToken;
      Expect(tkObject);
      if CurToken = tkObject then
        Result.IsMethodPointer := True;
      NextToken;
    end;
    if CurToken = tkSemicolon then
      NextToken;
    if (CurToken = tkIdentifier) and IsCallConv(CurTokenString, cc) then
    begin
      // Analyze the instruction up to '; '
      Result.CallConvention := cc;
      NextToken;
      while not EndOfDecl do
      begin
        Expect(tkIdentifier);
        if IsCallConv(CurTokenString, cc) then
          Result.CallConvention := cc
        else if IsModifier(CurTokenString, M) then // ignore
        else
          ParseError('Invalid procedural directive %s', [CurTokenString]);
        NextToken;
      end;
    end
    else if CurToken <> tkEqual then
      UngetToken;
  end;

  function ParseArrayType: TType;
  var
    IsDyn: boolean;
    A1, LastArr: TArrayType;
    Typ: TType;
  begin;
    NextToken; // skip 'array'
    LastArr :=
      nil;
    if CurToken = tkSquaredBraceOpen then
    begin
      IsDyn := False;
      Result := nil;
      NextToken;
      repeat
        A1 := TArrayType(CreateType(TArrayType));
        Typ := ParseType(False);
        if (Typ <> nil) and Typ.IsOrdinal then
        begin
          case Typ.TypeCode of
            typEnum: TArrayType(A1).Range := GetSubrangeType(TEnumType(Typ));
            typSubrange: TArrayType(A1).Range := TSubrangeType(Typ);
            else
              TArrayType(A1).Range := FContext.GetSubrangeType(Typ);
          end;
        end;
        if A1.Range = nil then
          A1.Range :=
            FContext.FBoolRangeType;
        if Result = nil then
          Result := A1;
        if LastArr <> nil then
          LastArr.ElementType := A1;
        LastArr := A1;
        if CurToken <> tkComma then
          Break;
        NextToken;
      until False;
      Expect(tkSquaredBraceClose);
      NextToken;
    end
    else
    begin
      IsDyn := True;
      Result := CreateType(TDynamicArrayType);
    end;
    Expect(tkOf);
    NextToken;
    Typ := ParseTypeDecl;
    if IsDyn then
      TDynamicArrayType(Result).ElementType := Typ
    else
      LastArr.ElementType := Typ;
    //  TArrayType(Result).ElementType := Typ;
    if psInPacked in FCurStates then
      TArrayType(Result).IsPacked := True;
    if IsDyn then
      Result.Size := FPointerSize
    else
      TArrayType(Result).Update;
  end;

  function ParseSetType: TSetType;
  var
    T: TType;
    RangeType: TSubrangeType;
  begin
    NextToken; // skip 'set'
    Expect(tkOf);
    NextToken;
    T := ParseType(False);
    if T.IsOrdinal then
    begin
      if not Assigned(T.Parent) then
        T.Parent := Parent;
      case T.TypeCode of
        typSubrange: RangeType := TSubrangeType(T);
        typEnum: RangeType := GetSubrangeType(TEnumType(T));
        else
          RangeType := FContext.GetSubrangeType(T);
      end;
      if RangeType.RangeEnd - RangeType.RangeBegin + 1 > 256 then
        ParseError('Sets may have at most 256 elements');
      Result := GetSetType(RangeType);
    end
    else
    begin
      ParseError(SErr_ExpectOrdinal);
      Result := FContext.FByteSetType;
    end;
  end;

  // Returns true, the type is acceptable
  function CheckFileType(Typ: TType): boolean;
  var
    I: integer;
  begin
    if Typ = nil then
    begin
      Result := True;
      Exit;
    end;
    Result := False;
    case Typ.TypeCode of
      typFile..typText: ParseError('File type not allowed in here');
      typString: if not TStringType(Typ).IsShortString then
          ParseError('Type need finalization, not allowed in file type');
      typVariant, typDynamicArray, typInterface: ParseError('Type need finalization, not allowed in file type');
      typArray: Result := CheckFileType(TArrayType(Typ).ElementType);
      typRecord: for I := 0 to TRecordType(Typ).Symbols.Count - 1 do
        begin
          Result := CheckFileType(TField(TRecordType(Typ).Symbols[I]).FieldType);
          if not Result then
            Exit;
        end;
      else
        Result := True;
    end;
  end;

  function ParseFileType: TFileType;
  var
    Typ: TType;
  begin
    NextToken; // skip 'file'
    if CurToken = tkOf then
    begin
      NextToken;
      Typ := ParseTypeDecl;
      Result := TFileType(CreateType(TFileType));
      Result.ElementType := Typ;
      CheckFileType(Result.ElementType);
    end
    else
      Result := TFileType(FContext.FFileType);
  end;

  function ParsePackedType: TType;
  var
    StateInfo: TParseStateInfo;
  begin
    NextToken;
    if CurToken in [tkFile, tkSet, tkArray, tkRecord, tkClass] then
    begin
      StateSet(psInPacked, StateInfo);
      Result := ParseTypeDecl;
      StateRestore(StateInfo);
    end
    else
    begin
      ParseError('Packed not allow here');
      Result := nil;
    end;
  end;

  function ParseShortString: TStringType;
  begin
    Result := TStringType(CreateElement(TStringType));
    NextToken;
    Result.Kind := strAShort;
    Result.CharCount := Self.ParseIntExpr(1);
    if Result.Size > 255 then
    begin
      ParseError(
        SErr_ShortStrSize);
      Result.CharCount := 255;
    end;
    Result.Update;
    Expect(tkSquaredBraceClose);
    NextToken;
  end;

begin
  {
  <TypeDecl>		::= <TypeId> '=' <TypeSpec>
  			  | SynError ';'
  }
  // Analyze the type until '; 'or'=' appears
  case CurToken of
    tkBraceOpen:
    begin // enum
      Result := CreateType(TEnumType);
      ParseEnumType(TEnumType(Result));
      TEnumType(Result).MinEnumSize := FMinEnumSize;
      TEnumType(Result).Update;
    end;
    tkCaret:
    begin // pointer
      NextToken;
      Expect(tkIdentifier);
      Result := ParsePointerType;
    end;
    tkIdentifier, tkIntConst, tkHexConst, tkCharConst, tkStrConst: Result := ParseType(not (psInVar in FCurStates));
    tkType:
    begin // My = type Byte;
      if (psInVar in FCurStates) or (psInField in FCurStates) then
        Expect(tkIdentifier);
      NextToken;
      if CurToken <> tkString then
        Expect(
          tkIdentifier);
      Result := ParseTypeName(True); // You can use parseQSym
    end;
    tkProcedure: Result := ParseProceduralType;
    tkFunction: Result := ParseProceduralType;
    tkRecord: Result := ParseRecordType(TypName, Parent);
    tkString:
    begin
      NextToken;
      if CurToken = tkSquaredBraceOpen then
        Result := ParseShortString
      else
        Result := FContext.FStringType;
    end;
    tkPacked: Result := ParsePackedType;
    tkArray: Result := ParseArrayType;
    tkSet: Result := ParseSetType;
    tkFile: Result := ParseFileType;
    else
      Result := nil;
  end;
  if Result = nil then
    Result := FContext.FIntegerType;
  if Result.TypeCode in [typPointer, typClass, typClassRef, typInterface, typDynamicArray, typFile, typText] then
    Result.Size := FPointerSize
  else if Result.TypeCode = typProcedural then
  begin
    if TProceduralType(Result).IsMethodPointer then
      Result.Size := FPointerSize * 2
    else
      Result.Size := FPointerSize;
  end
  else if Result.TypeCode = typAlias then
    Result.Size := TAliasType(Result).RefType.Size
  else if Result.TypeCode = typClonedType then
    Result.Size := TClonedAliasType(Result).RefType.Size;
end;

function TParser.ParseTypeExpr: TExpr;
var
  S1: TParseStateInfo;
begin
  // Analyze type expressions
  {
  MySubrange = a.b * 2 div 1 .. 100;
  My2 = 1>2..True;
  My3 = sizeof(Integer)..Sizeof(Double)
  }
  Self.StateSet(psInTypeExpr, S1);
  Result := ParseExpr;
  Self.StateRestore(S1);
end;

function TParser.ParseTypeRef: TType;
var
  E: TExpr;
begin
  // CurToken is tkIdentifier / tkString
  if CurToken = tkString then
  begin
    Result := FContext.FStringType;
    NextToken;
    Exit;
  end;
  ParseQualifiedId();
  E := SimplifyQualId;
  FQId.Reset;
  Result := nil;
  // todo 1: The problem here is that if Expr is not a type symbol, there will be an error
  // as a: ptr
  if CheckExpr(E) then
  begin
    if E.OpCode = opMEMBER then
      E := TBinaryExpr(E).Right;
    with TSymbolExpr(E) do
      if reference.NodeKind = nkType then
        Result := TType(reference);
  end;
  ReleaseExpr(E);
  if Result = nil then
    Result := FContext.FAnytype;
end;

procedure TParser.ParseTypeSection(Parent: TSymbol);

  procedure CheckUnresolved(Typ: TType);
  var
    Ref, Resolved: TType;
    Sym: TSymbol;
  begin
    while Typ <> nil do
    begin
      if typ.TypeCode = typClassRef then
        Ref := TClassRefType(typ).RefType
      else if typ.TypeCode = typPointer then
        Ref := TPointerType(typ).RefType
      else
        Ref := nil;
      if Ref = nil then
        Continue;
      Resolved := nil;
      Sym := FindSymbol(TUnresolvedType(Ref).Name);
      if Sym = nil then
        ParseError(typ.Coord, SErr_UnresolvedIdent, [TUnresolvedType(Ref).Name])
      else if Sym.NodeKind <> nkType then
        ParseError(typ.Coord, SErr_SymbolNotType, [TUnresolvedType(Ref).Name])
      else
        Resolved := TType(Sym);
      if typ.TypeCode = typClassRef then
      begin
        if Resolved = nil then
          Resolved := FContext.FTObjectType;
        TClassRefType(typ).RefType := TClassType(Resolved);
      end
      else if typ.TypeCode = typPointer then
      begin
        if Resolved = nil then
          Resolved := FContext.FIntegerType;
        TPointerType(typ).RefType := Resolved;
      end;
      Ref.Free; // this type is not added to FNodes
      Ref := Typ;
      Typ := TType(Typ.Next);
      Ref.Next := nil;
    end;
  end;

{ procedure NextT;
  var
    StateInfo: TParseStateInfo;
  begin
    StateSet(psInClass, StateInfo);
    NextToken;
    StateRestore(StateInfo);
  end; }
var
  Typ, T2: TType;
  StateInfo: TParseStateInfo;
  TypName: string;
  Unresolved: TType;
  Noname, NotAddSym: boolean;

  procedure AddUnresolved(Sym: TType);
  begin
    Sym.Next := Unresolved;
    Unresolved := Sym;
  end;

begin
  {
  <TypeSection>		::= TYPE <TypeDeclList>

  <TypeDeclList>		::= <TypeDecl>
  			  | <TypeDeclList>  <TypeDecl>
  }
  NextToken; // skip 'type'
  Expect(tkIdentifier);
  StateSet(psInType, StateInfo);
  Unresolved := nil;
  while CurToken = tkIdentifier do
  begin
    TypName := CurTokenString;
    NextToken;
    Expect(tkEqual);
    NextToken;
    Noname := False;
    NotAddSym := False;
    case CurToken of
      tkClass:
      begin
        // In class, private and the like become keywords to prevent Scanner from scanning these words for generic identifiers
        Scanner.EnableScopeKeyWords(True);
        NextToken;
        if CurToken = tkOf then
          Typ := ParseClassRefType
        else
          Typ := ParseClassType(TypName, Parent, NotAddSym);
        Scanner.EnableScopeKeyWords(False);
      end;
      tkRecord:
      begin
        Scanner.EnableScopeKeyWords(True);
        Typ := ParseRecordType(TypName, Parent);
        Scanner.EnableScopeKeyWords(False);
        NotAddSym := True;
      end;
      tkInterface, tkDispInterface: Typ := ParseInterfaceType(TypName, Parent, NotAddSym);
      tkObject:
      begin
        Scanner.EnableScopeKeyWords(True);
        Typ := ParseObjectType(TypName);
        Scanner.EnableScopeKeyWords(False);
        NotAddSym := True;
      end;
      else
        Typ := ParseTypeDecl(TypName, Parent);
        Noname := True;
    end;
    if (Typ.Name <> '') and Noname then
    begin
      T2 := Typ;
      Typ := CreateType(TAliasType);
      TAliasType(Typ).RefType := T2;
    end;
    if Typ.Name = '' then
      Typ.Name := TypName;
    if not NotAddSym then
      AddSymbol(Typ);
    Typ.Visibility := FCurVisibility;
    case Typ.TypeCode of
      typClassRef: if TClassRefType(Typ).RefType.TypeCode = typUntype then
          AddUnresolved(Typ);
      typPointer: if TPointerType(Typ).RefType.TypeCode = typUntype then
          AddUnresolved(Typ);
    end;
    Expect(tkSemicolon);
    NextToken;
  end;
  StateRestore(StateInfo);
  CheckUnresolved(Unresolved);
end;

function TParser.ParseUnit: TModule;
begin
  FModule := TModule(CreateElement(TModule));
  ParseUnitInterface(FModule);
  ParseUnitImplementation;
  Result := FModule;
end;

procedure TParser.ParseUnitImplementation;
  // Add the one marked as saInternal in Symbols to InternalSymbols;
  procedure CleanupSym;
  var
    globalst, localst: TSymbolTable;
    i, Count: integer;
    sym: TSymbol;

    procedure CleanupFunc(sym: TFunctionDecl);
    var
      gf, lf, f: TFunctionDecl;
    begin
      gf := nil;
      lf := nil;
      while sym <> nil do
      begin
        f := sym.NextOverload;
        if saInternal in sym.Attr then
        begin
          if lf = nil then
            lf := sym
          else
            lf.NextOverload := sym;
        end
        else
        begin
          if gf = nil then
            gf := sym
          else
            gf.NextOverload := sym;
        end;
        sym.NextOverload := nil;
        sym := f;
      end;
      if gf <> nil then
        globalst.Add(gf);
      if lf <> nil then
        localst.Add(lf);
    end;

  begin
    Count := 0;
    for i := 0
      to FModule.Symbols.Count - 1 do
    begin
      if saInternal in FModule.Symbols[i].Attr then
        Inc(Count);
    end;
    if Count = 0 then
      Exit;
    if Count = FModule.Symbols.Count then
    begin
      localst := FModule.InternalSymbols;
      FModule.Symbols := FModule.InternalSymbols;
      FModule.Symbols := localst;
      Exit;
    end;
    globalst := nil;
    localst := nil;
    try
      globalst := TSymbolTable.Create(FModule);
      localst := TSymbolTable.Create(FModule);
      localst.Capacity := Trunc(Count * 1.39);
      globalst.Capacity := Trunc((FModule.Symbols.Count - Count) * 1.39);
      globalst.AutoAddToOwner := False;
      localst.AutoAddToOwner := False;
      for i := 0 to FModule.Symbols.Count - 1 do
      begin
        sym :=
          FModule.Symbols[i];
        if sym.NodeKind in [nkFunc, nkMethod, nkExternalFunc] then
          CleanupFunc(TFunctionDecl(sym))
        else if saInternal in sym.Attr then
          localst.Add(sym)
        else
          globalst.Add(sym);
      end;
      globalst.AutoAddToOwner := True;
      localst.AutoAddToOwner := True;
    except
      globalst.Free;
      localst.Free;
      raise;
    end;
    FModule.Symbols.Free;
    FModule.Symbols := globalst;
    FModule.InternalSymbols.Free;
    FModule.InternalSymbols := localst;
  end;

  procedure CleanupUnit;
  var
    i: integer;
    newSt: TSymbolTable;
  begin
    if FModule.LoadedUnits.Count < 2 then
      Exit;
    newSt := TSymbolTable.Create(nil);
    newSt.AutoAddToOwner := False;
    newSt.Capacity := FModule.LoadedUnits.Count;
    for i := 0 to FModule.LoadedUnits.Count - 1 do
    begin
      if not (saInternal in FModule.LoadedUnits[i].Attr) then
        newSt.Add(FModule.LoadedUnits[i]);
    end;
    FModule.LoadedUnits.Free;
    FModule.LoadedUnits := newSt;
  end;

begin
  Expect(tkImplementation);
  ParseImplementSection;
  Expect(tkDot);
  FCurParent := nil;
  FCurStates := [];
  LeaveScope;  // pop global symbols
  // Check that all declarations are implemented
  CheckForward;
  if FErrorCount = 0 then
  begin
    CleanupSym;
    CleanupUnit;
  end;
end;

procedure TParser.ParseUnitInterface(M: TModule);

  procedure AddNameScopes(M: TModule);
  var
    I: integer;
    Ns, Prev: TNameScope;
  begin
    if Length(M.Names) = 0 then
    begin
      CurSymbols.AutoAddToOwner := False;
      AddSymbol(M);
      CurSymbols.AutoAddToOwner := True;
    end
    else
    begin
      Prev := nil;
      for I := 0 to High(M.Names) do
      begin
        Ns := TNameScope(CreateElement(TNameScope));
        Ns.Name := M.Names[I];
        if I = 0 then
          AddSymbol(Ns)
        else
          Prev.Add(Ns.Name, Ns);
        Prev := Ns;
      end;
    end;
  end;

begin
  {
  <Unit>			::= <UnitHeader>  <InterfaceSection> <ImplementationSection> <InitSection> '.'
  <UnitHeader>		::= UNIT <QualId> <OptPortDirectives> ';'
  }
  if CurToken <> tkUnit then
    NextToken;
  Expect(tkUnit);
  NextToken; // skip 'unit'
  FModule := M;
  FModule.TimeStamp := FScanner.TimeStamp;
  // Analysis unit name
  ParseQualifiedId;
  if FQId.CountOfNames = 1 then
    FModule.Name := FQID.Name
  else
    FModule.SetNameScope(FQID.Names, FQID.CountOfNames);
  FQID.Reset;
  if CurToken <> tkSemicolon then
  begin
    FModule.Hints := ParseHints;
    Expect(tkSemicolon);
  end;
  FContext.FModules.Add(FModule);
  if FIsSystemUnit then
    if not SameText('System', FModule.Name) then
      ParseError(SErr_SystemUnitNameMismatch, True);
  Expect(tkSemicolon);
  NextToken;
  Expect(tkInterface);
  if FIsSystemUnit then
  begin
    FModule := FContext.FSystemUnit;
  end;
  EnterScope(FModule.Symbols);
  AddNameScopes(FModule);
  if not FIsSystemUnit then
  begin
    FContext.LoadSystemUnit;
    FModule.Symbols.AutoAddToOwner := False;
    AddSymbols(FContext.FSystemUnit);
    FModule.Symbols.AutoAddToOwner := True;
    FModule.LoadedUnits.Add(FContext.FSystemUnit);
  end;
  FCurParent := FModule;
  //  SetTempExpr(True);
  ParseInterfaceSection;
  Expect(tkImplementation);
end;

procedure TParser.ParseUsesClause;
var
  M: TModule;
  Coord: TAstNodeCoord;
begin
  if FIsSystemUnit then
    ParseError(SErr_SystemUnitUsesOthers, True);
  {
  <UsesClause>		::= USES <IdList> ';'
  			  | SynError
  }
  NextToken; // skip 'uses'
  // todo 5: Ignore the use in statement for the time being
  while True do
  begin
    Expect(tkIdentifier);
    M := FContext.LoadUnit(CurTokenString);
    if (M.State in [msIntfCompiling, msLoading]) or SameText(FModule.Name, CurTokenString) then
    begin
      Coord.Row := FScanner.CurRow;
      Coord.Col := FScanner.CurColumn;
      Coord.FileName := FScanner.CurFileName;
      ParseError(Coord, SErr_CircularUnitReference, [FModule.Name, CurTokenString], True);
    end;
    FModule.LoadedUnits.Add(M);
    if Self.FInternalSection then
      Include(M.Attr, saInternal)
    else
      Exclude(M.Attr, saInternal);
    Self.AddSymbols(M);
    NextToken;
    if CurToken <> tkComma then
      Break;
    NextToken; // skip tkComma
  end;
  Expect(tkSemicolon);
  NextToken;
end;

procedure TParser.ParseVarSection(Parent: TSymbol);
  // todo 1: There is a problem, sometimes you need to return TMultiAccessor
  function ParseAbsVar: TSymbol;

    function FindField(Typ: TType; const S: string): TSymbol;
    begin
      case Typ.TypeCode of
        typRecord:
          Result := TRecordType(Typ).FindSymbol(S);
        typObject: Result := TObjectType(Typ).FindSymbol(S);
        typClass: Result := TClassType(Typ).FindSymbol(S);
        else
          Result := nil;
      end;
    end;

  var
    I: integer;
    Sym: TSymbol;
  begin
    {
    type
      TMyD = record
        a: string[20];
      end;
      PMyd = ^TMyd;
    var
      D: TmyD;
      P: PMyd = @D;
      StrLen1: Byte absolute D.a;   // ok
      StrLen2: Byte absolute D; // ok
      StrLen3: Byte absolute P.a;   // error
  }
    ParseQualifiedId;
    if FQId.CountOfNames = 1 then
      Result := FindSymbol(FQId.Name)
    else
    begin
      Sym := FindSymbol(FQId.Name);
      for I := 1 to FQID.CountOfNames - 1 do
      begin
        if not Assigned(Sym) then
          Break;
        case Sym.NodeKind of
          nkModule: Sym := TModule(Sym).FindSymbol(FQId.Names[I]);
          nkNameScope: Sym := TNameScope(Sym).FindSymbol(FQId.Names[I]);
          nkVariable:
          begin
            Sym := FindField(TVariable(Sym).VarType, FQId.Names[I]);
            if Assigned(Sym) then
              if Sym.NodeKind <> nkField then
              begin
                ParseError(SErr_FieldRequired);
                Sym := nil;
              end;
          end;
          nkType:
          begin
            Sym := FindField(TType(Sym), FQId.Names[I]);
            if Assigned(Sym) then
              if Sym.NodeKind <> nkField then
              begin
                ParseError(SErr_FieldRequired);
                Sym :=
                  nil;
              end
              else if not (saStatic in TField(Sym).Attr) then
              begin
                ParseError(SErr_StaticRequired);
                Sym := nil;
              end;
          end;
          else
            Sym := nil;
        end;
        if Sym = nil then
          Break;
        if not IsVisible(FCurParent, Sym) then
          ParseError(SErr_SymbolNotAccess, [Sym.Name]);
      end;
      if Assigned(Sym) then
        if Sym.NodeKind in [nkVariable, nkField] then
        begin
          ParseError(SErr_VarRequired);
          Sym := nil;
        end;
      Result := Sym;
    end;
  end;

var
  Typ, ValT: TType;
  Variable, V1: TVariable;
  //  E: TExpr;
  //  HasVal: Boolean;
  IsTls: boolean;
  Hints: TMemberHints;
  StateInfo: TParseStateInfo;
begin
  {
  <VarSection>		::= VAR <VarDeclList>

  <VarDeclList>		::= <VarDecl>
  			  | <VarDeclList>  <VarDecl>

  <VarDecl>		::= <IdList> ':' <Type> <OptAbsoluteClause> <OptPortDirectives> ';'
  			  | <IdList> ':' <Type> '=' <TypedConstant> <OptPortDirectives> ';'
  			  | <IdList> ':' <TypeSpec>
  			  | SynError ';'
  }
  // current token is tkType
  IsTls := CurToken = tkThreadVar;
  NextToken; // skip 'var' / 'threadvar'
  Expect(tkIdentifier);
  StateSet(psInVar, StateInfo);
  while CurToken = tkIdentifier do
  begin
    // parse variable list
    Variable := TVariable(ParseIdList(TVariable));
    Expect(tkColon);
    NextToken; // skip ':'
    Typ :=
      ParseTypeDecl;
    Hints := [];
    if CurToken = tkAbsolute then
    begin
      if IsTls then
        ParseError('Thread local variables cannot be ABSOLUTE', True);
      if Variable.Next <> nil then
        ParseError(SErr_AbsoluteVarList, True);
      NextToken;
      Variable.AbsVar := ParseAbsVar;
      if CurToken = tkEqual then
        ParseError(SErr_InitAbsoluteVar);
    end
    else
    //    if CurToken = tkIdentifier then // parse hint
      Hints := ParseHints;
    //    HasVal := False;
    if CurToken = tkEqual then
    begin
      if IsTls then
        ParseError(SErr_ThreadVarInit, True);
      if Assigned(Variable.Next) then
        ParseError(SErr_MultiVariablesInit, True);
      NextToken; // skip '=';
      ValClear(FTempValue);
      // parse init value
      case Typ.TypeCode of
        typArray:
        begin
          ParseConstArray(TArrayType(Typ), FTempValue);
          Variable.Value.VT := vtArray;
          Variable.Value.VArray := FTempValue.VArray;
          FTempValue.VT := vtEmpty;
        end;
        typRecord:
        begin
          ParseConstRecord(TRecordType(Typ), FTempValue);
          Variable.Value.VT := vtRecord;
          Variable.Value.VRecord := FTempValue.VRecord;
          FTempValue.VT := vtEmpty;
        end;
        else
          if ParseConstSimpleValue(Typ, FTempValue, ValT) then
          begin
            if not CheckAssignCompatibility(Typ, ValT) then
              ParseError(SErr_AssignIncomp);
          end
          else
            ValDefault(FTempValue, Typ);
          ValCopy(Variable.Value, FTempValue);
      end;
    end;
    V1 := Variable;
    repeat
      //      if HasVal then
      //        V1.Value := ValCopy(FTempValue);
      V1.VarType := Typ;
      V1.Hints := Hints;
      V1.Visibility := Self.FCurVisibility;
      if IsTls then
        Include(V1.VarAttr, vaTls);
      if Parent.NodeKind in [nkMethod, nkFunc] then
        Include(V1.VarAttr, vaLocal);
      AddSymbol(V1);
      if Parent.NodeKind in [nkFunc, nkMethod] then
        V1.Level := TFunction(Parent).Level;
      V1 := TVariable(V1.Next);
    until V1 = nil;
    ValClear(FTempValue);
    Expect(tkSemicolon);
    NextToken;
  end;
  StateRestore(StateInfo);
end;

function TParser.ParseWhileStmt: TWhileStmt;
var
  StateInfo: TParseStateInfo;
begin
  NextToken; // skip 'while'
  Result := TWhileStmt(CreateStmt(TWhileStmt));
  Result.Condition := ParseExpr;
  CheckBoolExpr(Result.Condition);
  Expect(tkDo);
  NextToken;
  StateSet(psInWhileStmt, StateInfo);
  Result.Stmt := ParseStatement(Result);
  StateRestore(StateInfo);
end;

function TParser.ParseWithStmt(Parent: TStatement): TCompoundStmt;

  function GetUniqueLocalName: string;
  var
    I: integer;
  begin
    I := 1;
    repeat
      Result := Format('$with%d', [I]);
      if Self.CurSymbols.Find(Result) = nil then
        Break;
      Inc(I);
    until False;
  end;

var
  E: TExpr;
  Deepth: integer;
  V: TVariable;
  AssStmt: TAssignmentStmt;
  Stmt: TStatement;
begin
  NextToken; // skip 'with'
  Deepth := FWithList.Count;
  Result := TCompoundStmt(CreateStmt(TCompoundStmt));
  repeat
    E := ParseExpr;
    if CurToken <> tkDo then
    begin
      Expect(tkComma);
      NextToken;
    end;
    {
      with getobj(a,b) do
        dosome;
      ==> Expands to:
      $with1 = getobj(a,b);
      $with1.dosome;
    }
    // Consider how you should proceed with the analysis if E is invalid
    // Processing: E.Typ = TObject
    if not CheckExpr(E) then
      E.Typ := FContext.FTObjectType
    else if not (E.Typ.TypeCode in [typClass, typInterface, typRecord, typObject]) then
    begin
      E.Typ := FContext.FTObjectType;
      ParseError(SErr_ExpectStructType);
    end;
    if E.OpCode = opSYMBOL then // In this case, E points to a Var/const
      EnterWithStmt(TSymbolExpr(E))
    else
    begin
      // Create a new local variable
      // If the pointer is to record or object, only the pointer is used
      V := TVariable(CreateElement(TVariable));
      V.Name := GetUniqueLocalName;
      if E.OpCode = opINST then
        V.VarType := TUnaryExpr(E).Operand.Typ
      else if E.Typ.TypeCode in [typRecord, typObject] then
      begin
        E.Typ.CreatePointerType(FPointerSize);
        V.VarType := E.Typ.PointerType;
      end
      else
        V.VarType := E.Typ;
      Include(V.VarAttr, vaHidden);
      AddSymbol(V);
      // Then create a new assignment statement, (if E is already invalid, then the assignment is invalid as well)
      AssStmt := TAssignmentStmt(CreateStmt(TAssignmentStmt));
      AssStmt.Left := CreateSymbolExpr(V.Name);
      AssStmt.Left.Typ := V.VarType;
      TSymbolExpr(AssStmt.Left).reference := V;
      EnterWithStmt(TSymbolExpr(AssStmt.Left));
      if E.OpCode = opINST then
      begin
        E := TUnaryExpr(E).Operand;
        E.Detach;
        AssStmt.Right := E;
      end
      else if E.Typ.TypeCode in [typRecord, typObject] then
      begin
        AssStmt.Right := CreateUnaryExpr(opADDR, E);
        AssStmt.Right.Typ := V.VarType;
      end
      else
        AssStmt.Right := E;
      AssStmt.Parent := Result;
      Result.Statements.Add(AssStmt);
    end;
  until CurToken = tkDo;
  NextToken; // skip 'do'
  Stmt := ParseStatement(Result);
  if Stmt <> nil then
    Result.Statements.Add(Stmt);
  // leave scope
  while Deepth < FWithList.Count do
    LeaveWithStmt;
end;

procedure TParser.ReleaseExpr(E: TExpr);
var
  i: integer;
begin
  if E = nil then
    Exit;
  case OpKinds[E.OpCode] of
    opkUnary:
    begin
      ReleaseExpr(TUnaryExpr(E).Operand);
      FContext.ReleaseExpr(E);
    end;
    opkBinary:
    begin
      ReleaseExpr(TBinaryExpr(E).Left);
      ReleaseExpr(
        TBinaryExpr(E).Right);
      FContext.ReleaseExpr(E);
    end;
    opkList:
    begin
      for i := 0 to TListExpr(E).Count - 1 do
        ReleaseExpr(TListExpr(E).Items[i]);
      FContext.ReleaseExpr(E);
    end;
    else
      FContext.ReleaseExpr(E);
  end;
end;

function TParser.SimplifyQualId: TExpr;

  function CloneSymbolExpr(Source: TSymbolExpr): TSymbolExpr;
  begin
    Result := CreateSymbolExpr(Source.Name);
    TSymbolExpr(Result).reference := Source.reference;
    TSymbolExpr(Result).Typ := Source.Typ;
    Result.Coord := Source.Coord;
  end;

var
  Sym: TSymbol;
  Prefix: TSymbolExpr;
  I: integer;
  InValid: boolean;
begin
  // Simplifications such as System.SysUtils.TStrings for this fully qualified identity
  // Take TStrings directly
  // If the System.SysUtils.TStrings identifier is invalid, it is not simplified
  if FindWith(FQId.Names[0], Prefix, Sym) then // in the with statement
  begin
    Prefix := CloneSymbolExpr(Prefix);
    if Prefix.Typ.TypeCode = typPointer then
    begin
      // dereference
      Result := CreateUnaryExpr(opINST, Prefix);
      Result.Typ := TPointerType(Prefix.Typ).RefType;
      //  Include(Result.Attr, eaVerified);
    end
    else
      Result := Prefix;
     // concat with Sym
    for I := 0 to
      FQId.CountOfNames - 1 do
      Result := CreateBinaryExpr(opMEMBER, Result, CreateSymbolExpr(FQId.Names[I]));
  end
  else
  begin
    Sym := FindSymbol(FQId.Names[0]);
    I := 1;
    while Assigned(Sym) and (I < FQId.CountOfNames) do
    begin
      case Sym.NodeKind of
        nkModule: Sym := TModule(Sym).FindSymbol(FQId.Names[I]);
        nkNameScope: Sym := TNameScope(Sym).FindSymbol(FQId.Names[I]);
        else
          Break;
      end;
      Inc(I);
    end;
    Result := nil;
    InValid := False;
    // If the identifier does not point to a valid symbol, the expression is not refined, but it is marked as invalid
    if (Sym = nil) or (Sym.NodeKind in [nkModule, nkNameScope]) or (I > FQId.CountOfNames) then
    begin
    // Don't report an error, wait for CheckExpr
    {  if Sym = nil then
        ParseError(SErr_UndeclaredIdent, [FQId.Names[I-1]])
      else
        ParseError(SErr_InvalidIdent, [Sym.Name]);}
      I := 0;
      InValid := True;
    end
    else
      Dec(I);
    while I < FQId.CountOfNames do
    begin
      if Result = nil then
      begin
        Result := CreateSymbolExpr(FQId.Names[I]);
        if not Invalid then
          TSymbolExpr(Result).reference := Sym;
      end
      else
        Result := CreateBinaryExpr(opMEMBER, Result, CreateSymbolExpr(FQId.Names[I]));
      Inc(I);
    end;
    if Invalid then
      Include(Result.Attr, eaInvalid);
  end;
end;

procedure TParser.StateClear(State: TParseState; out StateInfo: TParseStateInfo);
begin
  StateInfo.IsSet := State in FCurStates;
  StateInfo.State := State;
  Exclude(FCurStates, State);
end;

procedure TParser.StateRestore(const StateInfo: TParseStateInfo);
begin
  if StateInfo.IsSet then
    Include(FCurStates, StateInfo.State)
  else
    Exclude(FCurStates, StateInfo.State);
end;

procedure TParser.StateSet(State: TParseState; out StateInfo: TParseStateInfo);
begin
  StateInfo.IsSet := State in FCurStates;
  StateInfo.State := State;
  Include(FCurStates, State);
end;

function TParser.TryEvalConst(E: TExpr; out Value: TValueRec): boolean;
  procedure GetValue(E: TExpr; var V: TValueRec); forward;
  procedure DoEvalSet(un: TUnaryExpr; out Value: TValueRec); forward;
  procedure DoAddr(E: TExpr); forward;
const
  OrdRangeHighInt: array[TIntKind] of int64 = ($7F, $FF, $7FFF, $FFFF, $7FFFFFFF, $FFFFFFFF, $7FFFFFFFFFFFFFFF, $FFFFFFFFFFFFFFFF);
  OrdRangeHighChar: array[TCharKind] of word = ($FF, $FFFF);
  OrdRangeHighBool: array[TBoolKind] of longword = (1, $FF, $FFFF, $FFFFFFFF);
  OrdRangeLowInt: array[TIntKind] of int64 = (shortint($80), 0, smallint($8000), 0, longint($80000000), 0, int64($8000000000000000), 0);
  OrdRangeLowChar: array[TCharKind] of word = (0, 0);
  OrdRangeLowBool: array[TBoolKind] of longword = (0, 0, 0, 0);

  function CallHigh(E: TExpr): TValueRec;
  var
    Typ: TType;
    Ret: int64;
  begin
    Typ := E.Typ;
    if Typ.TypeCode = typInt then
      Ret := OrdRangeHighInt[TIntType(Typ).Kind]
    else if Typ.TypeCode = typChar then
      Ret := OrdRangeHighChar[TCharType(Typ).Kind]
    else if Typ.TypeCode = typBool then
      Ret := OrdRangeHighBool[TBoolType(Typ).Kind]
    else if Typ.TypeCode = typEnum then
      Ret := TEnumType(Typ).HighValue
    else if Typ.TypeCode = typSubrange then
      Ret := TSubrangeType(Typ).RangeEnd
    else if Typ.TypeCode = typArray then // typDynamicArray Constant evaluation does not work on dynamic arrays
      Ret := TArrayType(Typ).Range.RangeEnd
    else if Typ.IsAnsiShortString or Typ.IsWideShortString then
      Ret := TStringType(Typ).CharCount - 1
    else
    begin
      raise EEvalConstant.CreateCoordFmt(E.Coord, SErr_InvalidArgument, ['high']);
      Ret := 0;
    end;
    if Ret and $FFFFFFFF80000000 = 0 then
      Result := ValFromInt(integer(Ret))
    else
      Result := ValFromInt(Ret);
  end;

  function CallLow(E: TExpr): TValueRec;
  var
    Typ: TType;
    Ret: int64;
  begin
    Typ := E.Typ;
    if Typ.TypeCode = typInt then
      Ret := OrdRangeLowInt[TIntType(Typ).Kind]
    else if Typ.TypeCode = typChar then
      Ret := OrdRangeLowChar[TCharType(Typ).Kind]
    else if Typ.TypeCode = typBool then
      Ret := OrdRangeLowBool[TBoolType(Typ).Kind]
    else if Typ.TypeCode = typEnum then
      Ret := TEnumType(Typ).LowValue
    else if Typ.TypeCode = typSubrange then
      Ret := TSubrangeType(Typ).RangeBegin
    else if Typ.TypeCode = typArray then // typDynamicArray Constant evaluation does not work on dynamic arrays
      Ret := TArrayType(Typ).Range.RangeBegin
    else if Typ.IsAnsiShortString or Typ.IsWideShortString then
      Ret := 1
    else
    begin
      ParseError(E.Coord, SErr_InvalidArgument, ['low']);
      Ret := 0;
    end;
    if Ret and $FFFFFFFF80000000 = 0 then
      Result := ValFromInt(integer(Ret))
    else
      Result :=
        ValFromInt(Ret);
  end;

  function CallLength(E: TExpr): integer;
  var
    Typ: TType;
    V: TValueRec;
  begin
    Typ := E.Typ;
    case Typ.TypeCode of
      typArray: // typDynamicArray Cannot be used for constant estimation
        Result := TArrayType(Typ).Range.RangeEnd - TArrayType(Typ).Range.RangeBegin + 1;
      typString:
        if TStringType(Typ).IsShortString then
          Result := TStringType(Typ).CharCount
        else
        begin
          ValInit(V);
          try
            GetValue(E, V);
            // todo 1: If in Ansi mode, it should be converted to RawStr before getting the value
            Result := Length(ValToStr(V));
          finally
            ValClear(V);
          end;
        end;
      else
        ParseError(E.Coord, SErr_InvalidArgument, ['length']);
        Result := 0;
    end;
  end;

  // For example: Sizeof(['a'..'g']);
  // If there is an Expr that cannot be a value, it is treated as 32
  function SizeOfSetLiteral(E: TExpr): integer;
  var
    V: TValueRec;
  begin
    try
      ValInit(V);
      DoEvalSet(TUnaryExpr(E), V);
      Result := ValToSet(V).MinSize;
      ValClear(V);
    except
      ValClear(V);
      Result := 32;
    end;
  end;

  // sizeof can be used for types, variables, procedure/function names, and constant expressions
  function CallSizeOf(E: TExpr): cardinal;
  var
    Ref: TSymbol;
    S: TSetValue;
  begin
    if E.Typ.TypeCode = typSet then
    begin
      if E.OpCode = opSET then
        Result := SizeOfSetLiteral(E)
      else if OpKinds[E.OpCode] = opkConst then
      begin
        S := ValToSet(TConstExpr(E).Value);
        if S = nil then
          Result := 32
        else
          Result := S.MinSize;
      end
      else
      begin
        Ref := E.GetReference;
        if (Ref <> nil) and (Ref.NodeKind = nkConstant) then
        begin
          S := ValToSet(TConstant(Ref).Value);
          if S = nil then
            Result := 32
          else
            Result := S.MinSize;
        end
        else
          Result := E.Typ.Size;
      end;
    end
    else
      Result := E.Typ.Size;
  end;

  procedure DoCall(bin: TBinaryExpr);

    function CheckInt(const V: TValueRec; const Func: string): boolean;
    begin
      Result := V.VT in [vtInt, vtInt64];
      if not Result then
        raise EEvalConstant.CreateCoordFmt(bin.Coord, SErr_InvalidArgument, [Func]);
    end;

    function CheckOrd(const V: TValueRec; const Func: string): boolean;
    begin
      Result := V.VT in [vtInt, vtInt64, vtAChr, vtWChr, vtBool];
      if not Result then
        raise EEvalConstant.CreateCoordFmt(bin.Coord, SErr_InvalidArgument, [Func]);
    end;

    function CheckNum(const V: TValueRec; const Func: string): boolean;
    begin
      Result := V.VT in [vtInt, vtInt64, vtReal, vtCurr];
      if not Result then
        raise EEvalConstant.CreateCoordFmt(bin.Coord, SErr_InvalidArgument, [Func]);
    end;

    function CheckIntTyp(A1: TExpr; const Func: string): boolean;
    begin
      Result := A1.Typ.TypeCode = typInt;
      if not Result then
        raise EEvalConstant.CreateCoordFmt(A1.Coord, SErr_InvalidArgument, [Func]);
    end;

  var
    A1: TExpr;
    F: TSymbol;
    V: TValueRec;
  begin
    F := bin.Left.GetReference;
    if (F = nil) or (F.NodeKind <> nkBuiltinFunc) then
      raise EEvalConstant.CreateCoord(bin.Coord, 'Invalid function in const expr');
    A1 := TListExpr(bin.Right).Items[0];
    ValInit(V);
    try
      if not (TBuiltinFunction(F).Kind in [bfAddr, bfHigh, bfLow, bfSizeOf, bfLength]) then
        GetValue(A1, V);
      case TBuiltinFunction(F).Kind of
        bfAbs: if CheckNum(V, 'abs') then
            Value := ValAbs(V);
        bfAddr: DoAddr(A1);
        bfChr: if CheckInt(V, 'chr') then
            Value := ValChr(V);
        bfHi: if CheckInt(V, 'hi') and CheckIntTyp(A1, 'hi') then
            Value := ValHi(V, TIntType(A1.Typ));
        bfHigh: Value := CallHigh(A1);
        bfLength: Value := ValFromInt(CallLength(A1));
        bfLo: if CheckInt(V, 'lo') and CheckIntTyp(A1, 'lo') then
            Value := ValLo(V, TIntType(A1.Typ));
        bfLow: Value := CallLow(A1);
        bfOdd: if CheckInt(V, 'odd') then
            Value := ValOdd(V);
        bfOrd: if CheckOrd(V, 'ord') then
            Value := ValOrd(V);
        bfPred: if CheckOrd(V, 'pred') then
            Value := ValPred(V);
        bfRound: if CheckNum(V, 'round') then
            Value := ValRound(V);
        bfSizeOf: Value := ValFromInt(int64(CallSizeOf(A1))); // ValFromInt(A1.Typ.Size);
        bfSucc: if CheckOrd(V, 'succ') then
            Value := ValSucc(V);
        bfSwap: if CheckInt(V, 'swap') and CheckIntTyp(A1, 'swap') then
            Value := ValSwap(V, TIntType(A1.Typ));
        bfTrunc: if CheckNum(V, 'trunc') then
            Value := ValTrunc(V);
        else
          raise EEvalConstant.CreateCoord(bin.Coord, SErr_InvalidBuiltinFunc);
      end;
    finally
      ValClear(V);
    end;
  end;

  procedure GetValue(E: TExpr; var V: TValueRec);
  begin
    if OpKinds[E.OpCode] = opkConst then
    begin
      ValCopy(V, TConstExpr(E).Value);
    end
    else if OpKinds[E.OpCode] = opkSymbol then
    begin
      case TSymbolExpr(E).reference.NodeKind
        of
        nkEnumElement: ValFromInt(V, TEnumValue(TSymbolExpr(E).reference).Value);
        nkConstant: ValCopy(V, TConstant(TSymbolExpr(E).reference).Value);
        nkType: if TType(TSymbolExpr(E).reference).TypeCode = typClass then
            ValFromSymbol(V, TSymbolExpr(E).reference);
        else
          raise ENotConstant.CreateCoord(E.Coord, SErr_ExpectConstExpr);
      end;
    end;
  end;

  // Calculate array element offset
  function CalcOffset(E: TExpr; T: TType; var Offset: int64): boolean;
  var
    i: integer;
    c, size: int64;
    V: TValueRec;
  begin
    // arr: array[0..1, 0..2] of byte;
    // @arr[1, 2];
    Assert(E.OpCode = opLIST, 'TryEvalConst$CalcOffset: Expect E.OpCode=opLIST');
    Assert(T.TypeCode = typArray, 'TryEvalConst$CalcOffset: Expect T.TypeCode=typArray');
    Result := False;
    size := 0;
    ValInit(V);
    for i := 0 to TListExpr(E).Count - 1 do
    begin
      if T.TypeCode <> typArray then
        Exit;
      GetValue(TListExpr(E).Items[i], V);
      c := ValToInt(V);
      c := c - TArrayType(T).Range.RangeBegin;
      size := size + c * TArrayType(T).ElementType.Size;
      ValClear(V);
      T := TArrayType(T).ElementType;
    end;
    Inc(Offset, size);
    Result := True;
  end;

  // Determine whether the expression can be decomposed into a symbol address and offset
  // Scenario assumption: var p: Pointer = @rec.a[1,2].val;
  function GetOffsetSym(E: TExpr; out S: TSymbol; out Offset: int64): boolean;
  var
    Ref: TSymbol;
  begin
    S := nil;
    Offset := 0;
    Result := False;
    while True do
    begin
      case E.OpCode of
        opSYMBOL:
        begin
          Ref := TSymbolExpr(E).reference;
          // variables, parameters, functions
          if Ref.NodeKind in [nkVariable, nkFuncParam, nkFunc, nkMethod, nkExternalFunc] then
          begin
            S := Ref;
            Result := True;
          end;
          Break;
        end;
        opMEMBER:
        begin
          Ref := TBinaryExpr(E).Right.GetReference;
          Assert(Ref <> nil);
          if Ref.NodeKind = nkField then
            Inc(Offset, TField(Ref).Offset);
          E := TBinaryExpr(E).Left;
        end;
        opINDEX: if not (eaArrayProp in E.Attr) and not (eaVarOp in E.Attr) and not
            (TBinaryExpr(E).Left.Typ.TypeCode <> typArray) then
          begin
            if not CalcOffset(TBinaryExpr(E).Right, TBinaryExpr(E).Left.Typ, Offset) then
              Break;
            E := TBinaryExpr(E).Left;
          end
          else
            Break;
        else
          Break;
      end;
    end;
  end;

  procedure DoAddr(E: TExpr);
  var
    S: TSymbol;
    Offset: int64;
  begin
    if GetOffsetSym(E, S, Offset) then
    begin
      if Offset > High(longint) then
        raise EEvalConstant.CreateCoord(E.Coord, 'Offset too large');
      ValFromAddrOffset(Value, S, integer(Offset));
    end
    else
      raise ENotConstant.CreateCoord(E.Coord, SErr_ExpectConstExpr);
  end;

  procedure DoCast(bin: TBinaryExpr);
  var
    A1: TExpr;
    F: TSymbol;
    V: TValueRec;
  begin
    F := bin.Left.GetReference;
    // CheckExpr has ensured that F.NodeKind = nkType
    if (F = nil) or (F.NodeKind <> nkType) then
      raise EEvalConstant.CreateCoord(bin.Coord, 'DoCast: Expect F is type');
    F := TType(F).NormalType;
    A1 := bin.Right;
    ValInit(V);
    try
      GetValue(A1, V);
      case TType(F).TypeCode of
        typInt: if TIntType(F).Kind in [intS8..intS32] then
            Value := ValCast(V, vtInt)
          else
            Value := ValCast(V, vtInt64);
        typNumeric: if TNumericType(F).Kind = numCurrency then
            Value := ValCast(V, vtCurr)
          else
            Value := ValCast(V, vtReal);
        typChar: if TCharType(F).Kind = charAnsi then
            Value := ValChr(V)
          else
            Value := ValFromWChar(widechar(word(ValToInt(V))));
        typBool: Value := ValCast(V, vtBool);
        typPointer, typPAnsiChar, typPWideChar: if V.VT <> vtAddrOffset then
            Value := ValCast(V, vtPtr)
          else
            Value := V;
        else
          Value := V;
      end;
    finally
      ValClear(V);
    end;
  end;

  procedure DoEval;
  var
    LVal, RVal: TValueRec;
  begin
    ValInit(Value);
    ValInit(LVal);
    ValInit(RVal);
    try
      case
        OpKinds[E.OpCode] of
        opkUnary: GetValue(TUnaryExpr(E).Operand, LVal);
        opkBinary:
        begin
          GetValue(TBinaryExpr(E).Left, LVal);
          GetValue(TBinaryExpr(E).Right, RVal);
        end;
        else
          GetValue(E, Value);
          Exit;
      end;
      case E.OpCode of
        opADD..opSHR: Value := ValOp(LVal, RVal, E.OpCode);
        opNE..opGE: Value := ValCmp(LVal, RVal, E.OpCode);
        opIN: Value := ValIn(LVal, RVal);
        opNOT: Value := ValNot(LVal);
        opNEG: Value := ValNeg(LVal);
        opPOS: Value := LVal;
        else
          raise EEvalConstant.CreateCoord(E.Coord, SErr_ExpectConstExpr);
      end;
    finally
      ValClear(LVal);
      ValClear(RVal);
    end;
  end;

  procedure DoEvalSet(un: TUnaryExpr; out Value: TValueRec);
  var
    Item: TExpr;
    List: TListExpr;
    V1, V2: TValueRec;
    S, S2: TSetValue;
    I, J: integer;
  begin
    ValInit(Value);
    Assert(un.Operand.OpCode = opLIST, 'DoEvalSet');
    List := TListExpr(un.Operand);
    if (List = nil) or (List.Count = 0) then
    begin
      S := TSetValue.Create;
      S.Update;
      ValFromSet(Value, S);
      Exit;
    end;
    ValInit(V1);
    ValInit(V2);
    S := TSetValue.Create;
    try
      for J := 0 to List.Count - 1 do
      begin
        Item := List.Items[J];
        // No need to judge. GetValue below automatically judges whether it is a constant
        // if not (eaConst in Item.Attr) then Exit;
        if Item.OpCode = opRANGE then
        begin
          ValClear(V1);
          ValClear(V2);
          GetValue(TBinaryExpr(Item).Left, V1);
          GetValue(TBinaryExpr(Item).Right, V2);
          for I := ValToInt(V1) to ValToInt(V2) do
            S.SetBits(I, True);
        end
        else
        begin
          ValClear(V1);
          GetValue(Item, V1);
          S.SetBits(ValToInt(V1), True);
        end;
      end;
      S.Update;
      S2 := TSetValue.Create;
      S2.Assign(S);
      ValFromSet(Value, S2);
    finally
      S.Free;
      ValClear(V1);
      ValClear(V2);
    end;
  end;

  procedure Err(E: EParserError);
  var
    Coord: TAstNodeCoord;
  begin
    Coord.FileName := E.FileName;
    Coord.Col := E.Column;
    Coord.Row := E.Row;
    ParseError(Coord, E.Message);
  end;

begin
  Result := False;
  try
    case E.OpCode of
      opCAST: DoCast(TBinaryExpr(E));
      opADDR: DoAddr(TUnaryExpr(E).Operand);
      opCALL: DoCall(TBinaryExpr(E));
      opSET: DoEvalSet(TUnaryExpr(E), Value);
      opSYMBOL, opCONST, opNIL:
      begin
        ValInit(Value);
        GetValue(E, Value);
      end
      else
        DoEval;
    end;
    Result := True;
  except
    // Check that the expression is not a constant, and return False without processing
    on ENotConstant do
      Result := False;
    // If EParserError is thrown, this message needs to be displayed with the specified Coord
    on Ex: EParserError do
      Err(Ex);
    // Others such as Assert, EASTError, indicating an error
    on Ex: Exception do
      InternalError(Ex.Message);
  end;
end;

function TParser.TryEvalGet(E: TExpr; var Value: TValueRec): boolean;
begin
  Assert(OpKinds[E.OpCode] in [opkConst, opkSymbol], 'TParser.TryEvalGet');
  ValClear(Value);
  Result := TryEvalConst(E, Value);
end;

procedure TParser.UngetToken(Step: integer);

  procedure Err;
  begin
    raise EParserError.Create(Format(SErr_InternalError, ['Cannot unget more tokens, history buffer is full']),
      Scanner.CurFileName, 0, 0);
  end;

begin
  if Step >= MAX_UNGET then
    Err;
  Dec(FTokenIndex, Step);
  if FTokenIndex < 0 then
    Inc(FTokenIndex, MAX_UNGET + 1);
  FCurToken := FTokenBuffer[FTokenIndex].Token;
  FCurTokenString := FTokenBuffer[FTokenIndex].TokenStr;
end;

constructor TFunctionHeader.Create;
begin
  Params := TFuncParamList.Create;
  Params.Capacity := 20;
  SetLength(Names, 10);
end;

destructor TFunctionHeader.Destroy;
begin
  Params.Free;
  inherited;
end;

procedure TFunctionHeader.Reset;
var
  i: integer;
begin
  Name := '';
  for i := 0 to CountOfNames - 1 do
    Names[i] := '';
  CountOfNames := 0;
  FileName := '';
  RoutineName := '';
  ImplementingName := '';
  RoutineNo := 0;
  MsgNo := 0;
  ReturnType := nil;
  Params.Count := 0;
  Directives := [];
  Modifiers := [];
  CallConvention := ccDefault;
  MethodKind := mkNormal;
  ObjectKind := okClass;
end;

constructor TQualifiedID.Create;
begin
  SetLength(Names, 10);
end;

function TQualifiedID.Id: string;
var
  I: integer;
begin
  Result := Name;
  for I := 1 to CountOfNames - 1 do
  begin
    if I = 1 then
      Result := Result + '.';
    Result := Result + Names[I];
  end;
end;

procedure TQualifiedID.Reset;
var
  I: integer;
begin
  Name := '';
  for I := 0 to CountOfNames - 1 do
    Names[I] := '';
  CountOfNames := 0;
end;

function TQualifiedID.SameScope(const Scopes: array of string): boolean;
var
  I: integer;
begin
  for I := 0 to High(Scopes) do
  begin
    if (I >= Length(Names)) or not SameText(Scopes[I], Names[I]) then
    begin
      Result := False;
      Exit;
    end;
  end;
  Result := True;
end;

end.
