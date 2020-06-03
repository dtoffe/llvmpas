unit ast;

{$I lpcdef.inc}

interface

uses Classes, SysUtils, hashtable;

const
  ROOT_VMT_OFFSET = 8;
  ROOT_VMT_ENTRY_COUNT = 19;

type
  TSymString = UTF8String;
  TMemberVisibility = (visDefault, visStrictPrivate, visStrictProtected, visPrivate, visProtected,
    visPublic, visPublished, visAutomated);
  TMemberVisibilities = set of TMemberVisibility;
  TMemberHint = (hDeprecated, hLibrary, hPlatform, hExperimental, hUnimplemented);
  TMemberHints = set of TMemberHint;
  TCallingConvention = (ccDefault, ccRegister, ccPascal, ccCDecl, ccStdCall, ccSafeCall);
  TModule = class;
  TCompoundStmt = class;
  TType = class;
  TArrayType = class;
  TRecordType = class;
  TInterfaceType = class;
  TVariable = class;
  TConstant = class;
  TFuncParamList = class;
  TFunctionDecl = class;
  TFunction = class;
  TStmtLabel = class;
  TSymbolTable = class;
  TAstNodeKind = (nkSymbol, nkExpr, nkType, nkNameScope, nkModule, nkVariable, nkConstant,
    nkField, nkProperty, nkIntfProperty, nkMethod, nkMethodResolution, nkFuncParam, nkEnumElement,
    nkFunc, nkExternalFunc, nkBuiltinFunc, nkAccessor, nkLabel, nkStmt, nkSymbolOffset);
  TAstNodeKinds = set of TAstNodeKind;
  EASTError = class(Exception);

  TAstNodeCoord = record
    FileName: string;
    Row, Col: integer;
  end;

  TAstNode = class
  private
    FNodeKind: TAstNodeKind;
  public
    Coord: TAstNodeCoord;
    Next: TAstNode;
  public
    constructor Create; virtual;
    destructor Destroy; override;
    property NodeKind: TAstNodeKind read FNodeKind;
  end;

  TAstNodeClass = class of TAstNode;
  TSymbolAttribute = (saUsed, saReserved1, saInternal, saForward, saStatic, saClass, saPrimitive, saTemp);
  TSymbolAttributes = set of TSymbolAttribute;

  TSymbol = class(TAstNode)
  private
    FName: TSymString;
    FParent: TSymbol;
    FHints: TMemberHints;
    function GetUnitName: string;
    function GetModule: TModule;
    function GetFullName: TSymString;
    function GetSymName: TSymString;
  protected
    procedure AddSymbol(Sym: TSymbol); virtual;
  public
    Attr: TSymbolAttributes;
    Visibility: TMemberVisibility;
    property Name: TSymString read FName write FName;
    property UnitName: string read GetUnitName;
    property Module: TModule read GetModule;
    property Parent: TSymbol read FParent write FParent;
    property Hints: TMemberHints read FHints write FHints;
    property FullName: TSymString read GetFullName;
    property SymName: TSymString read GetSymName;
    procedure Add(Sym: TSymbol); virtual;
  end;

  TSymbolClass = class of TSymbol;
  TValueType = (vtEmpty, vtInt, vtInt64, vtReal, vtCurr, vtSet, vtBool, vtStr, vtWStr, vtAChr,
    vtWChr, vtPtr, vtArray, vtRecord, vtSymbol, vtAddrOfSymbol, vtAddrOffset, vtIID, vtIIDStr);
  TValueTypes = set of TValueType;

  TSetValue = class
  public
    Bits: array[0..31] of byte;
    BitStart: byte;
    BitCount: byte;
    constructor Create;
    procedure Assign(Source: TSetValue);
    function IsEmpty: boolean;
    function AsString: string;
    function Include(R: TSetValue): boolean;
    function TestBits(Index: byte): boolean;
    function MinSize: integer;
    procedure SetBits(Index: byte; Value: boolean);
    procedure SetRange(Lo, Hi: byte; Value: boolean);
    procedure Update;
    function Equal(R: TSetValue): boolean;
    class function Add(L, R: TSetValue): TSetValue;
    class function Sub(L, R: TSetValue): TSetValue;
    class function Mul(L, R: TSetValue): TSetValue;
  end;

  TSymbolOffset = class(TSymbol)
  public
    Symbol: TSymbol;
    Offset: integer;
    Typ: TType;
  end;

  TArrayValue = class;
  TRecordValue = class;
  PValueRec = ^TValueRec;

  TValueRec = record
    VT: TValueType;
    Res1: word;
    Res2: word;
    Res3: word;
    case TValueType of
      vtInt: (VInt: integer);
      vtInt64: (VInt64: int64);
      vtReal: (VReal: double);
      vtCurr: (VCurr: currency);
      vtSet: (VSet: Pointer);
      vtBool: (VBool: cardinal);
      vtStr: (VStr: Pointer);
      vtWStr: (VWStr: Pointer);
      vtAChr: (VAChr: AnsiChar);
      vtWChr: (VWChr: integer);
      vtPtr: (VPtr: Pointer);
      vtSymbol: (VSymbol: TSymbol);
      vtAddrOfSymbol: (VAddr: TSymbol);
      vtArray: (VArray: TArrayValue);
      vtRecord: (VRecord: TRecordValue);
      vtIID: (VIID: TInterfaceType);
      vtIIDStr: (VIIDStr: Pointer);
  end;

  TArrayValueRange = record
    Start, Stop: integer;
  end;
  TArrayByteValues = array[0..High(integer) - 1] of byte;
  PArrayByteValues = ^TArrayByteValues;
  TArrayWordValues = array[0..High(integer) div 2 - 1] of word;
  PArrayWordValues = ^TArrayWordValues;
  TArrayDWordValues = array[0..High(integer) div 4 - 1] of cardinal;
  PArrayDWordValues = ^TArrayDWordValues;
  TArrayInt64Values = array[0..High(integer) div 8 - 1] of int64;
  PArrayInt64Values = ^TArrayInt64Values;
  TArrayPtrValues = array[0..High(integer) div SizeOf(Pointer) - 1] of Pointer;
  PArrayPtrValues = ^TArrayPtrValues;
  TArraySingleValues = array[0..High(integer) div SizeOf(single) - 1] of single;
  PArraySingleValues = ^TArraySingleValues;
  TArrayDoubleValues = array[0..High(integer) div SizeOf(double) - 1] of double;
  PArrayDoubleValues = ^TArrayDoubleValues;
  TArrayCurrencyValues = array[0..High(integer) div SizeOf(currency) - 1] of currency;
  PArrayCurrencyValues = ^TArrayCurrencyValues;
  TArrayBoolValues = array[0..High(integer) div SizeOf(boolean) - 1] of boolean;
  PArrayBoolValues = ^TArrayBoolValues;
  TArrayBounds = array of integer;

  TArrayValue = class
  private
    FBounds: TArrayBounds;
    FElementCount: integer;
    FElementType: TType;
    function GetElementCount: integer;
    function GetDimCount: integer;
  public
    Items: array of TValueRec;
    property DimCount: integer read GetDimCount;
    property Bounds: TArrayBounds read FBounds;
    procedure CreateValue(typ: TArrayType);
    procedure Assign(Source: TArrayValue);
    destructor Destroy; override;
    procedure Clear;
    function Put(Index: integer; var V: TValueRec): boolean;
  end;

  TRecordValue = class
  private
    FType: TRecordType;
    FElementCount: integer;
  public
    Items: array of TValueRec;
    destructor Destroy; override;
    procedure CreateValue(typ: TRecordType);
    procedure Assign(Source: TRecordValue);
    procedure Clear;
    function Put(Index: integer; var V: TValueRec): boolean;
    property ElementCount: integer read FElementCount;
  end;

  TFileTimeStamp = record
    Date: longword;
    Time: longword;
  end;
  TModuleKind = (mkUnit, mkProgram, mkPackage, mkDLL);
  TModuleState = (msNone, msLoading, msIntfCompiling, msImplCompiling, msSaved, msGenOk);

  TModule = class(TSymbol)
  private
    FType: TType;
    FPrivateNodes: TFPList;
  protected
    procedure AddSymbol(Sym: TSymbol); override;
  public
    PointerSize: byte;
    Kind: TModuleKind;
    State: TModuleState;
    Symbols: TSymbolTable;
    InternalSymbols: TSymbolTable;
    LoadedUnits: TSymbolTable;
    TimeStamp: TFileTimeStamp;
    InitializeFunc, FinalizeFunc: TFunction;
    FileName: string;
    Names: array of TSymString;
    Codes, Dump: string;
    constructor Create; override;
    destructor Destroy; override;
    function FindSymbol(const S: TSymString): TSymbol;
    function GetType: TType;
    procedure SetNameScope(const Scopes: array of TSymString; Count: integer);
    procedure Add(Sym: TSymbol); override;
    procedure AddPrivate(Node: TAstNode);
  end;

  TNameScope = class(TSymbol)
  private
    FType: TType;
    FSubNames: TStringList;
  public
    constructor Create; override;
    destructor Destroy; override;
    function FindSymbol(const S: TSymString): TSymbol;
    procedure Add(const S: TSymString; Sym: TSymbol); reintroduce;
    function GetType: TType;
  end;

  TPackage = class(TSymbol)
  public
    Modules: TFPList;
  end;

  TTypeCode = (typUnknown, typUntype, typInt, typNumeric, typBool, typChar, typPointer,
    typPAnsiChar, typPWideChar, typString, typVariant, typFile, typText, typProcedural, typRecord,
    typObject, typClass, typInterface, typClassRef, typEnum, typSet, typSubrange, typArray,
    typDynamicArray, typSymbol, typAlias, typClonedType, typOpenArray, typVector);
  TTypeCodes = set of TTypeCode;
  TBaseTypeCode = (btcUnknown, btcUntype, btcShortint, btcByte, btcSmallint, btcWord, btcLongint,
    btcLongWord, btcInt64, btcUInt64, btcComp, btcSingle,
    btcDouble, btcReal48, btcExtended, btcCurrency, btcBoolean, btcByteBool, btcWordBool,
    btcLongBool, btcAnsiChar, btcWideChar, btcPointer, btcPAnsiChar, btcPWideChar, btcAnsiString,
    btcWideString, btcUnicodeString, btcShortString, btcWShortString, btcVariant, btcOleVariant,
    btcFile, btcText, btcProcedural, btcRecord, btcObject, btcClass, btcInterface, btcDispInterface,
    btcClassRef, btcEnum, btcSet, btcSubrange, btcArray, btcDynamicArray, btcOpenArray);

  TType = class(TSymbol)
  private
    FSize: cardinal;
    FPointerType: TType;
    FTypeCode: TTypeCode;
  protected
    function GetAlignSize: byte; virtual;
  public
    constructor Create; override;
    destructor Destroy; override;
    property TypeCode: TTypeCode read FTypeCode;
    property Size: cardinal read FSize write FSize;
    property AlignSize: byte read GetAlignSize;
    property PointerType: TType read FPointerType;
    procedure CreatePointerType(ASize: cardinal);
    function BaseCode: TBaseTypeCode; {$IFNDEF DEBUG}inline;{$ENDIF}
    function OriginalType: TType;
    function NormalType: TType; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsOrdinal: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsReal: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsComp: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsCurrency: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsSingle: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsInteger: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsInt32: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsSignedInt: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsSigned: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsBoolean: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsStdBool: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsProcedural: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsMethodPointer: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsStringCompatible: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsStringArithCompatible: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsUnicodeString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsWideString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsAnsiString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsShortString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsAnsiShortString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsWideShortString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPackedString: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPackedStringAnsi: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPackedStringWide: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPAnsiChar: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPWideChar: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsVariantCompatible: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPointer: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsPointerBased: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function IsUntypePointer: boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
    function Equals(typ: TType): boolean; reintroduce;
  end;

  TTypeClass = class of TType;

  TPrimitiveType = class(TType)
  protected
    function GetAlignSize: byte; override;
  public
    FAlign: byte;
    constructor Create(ACode: TTypeCode); reintroduce; virtual;
  end;

  TUnresolvedType = class(TType)
  public
    constructor Create; override;
  end;

  TAliasType = class(TType)
  private
    FRefType: TType;
  public
    constructor Create; override;
    procedure Update;
    property RefType: TType read FRefType write FRefType;
  end;

  TClonedAliasType = class(TAliasType)
  public
    constructor Create; override;
  end;

  TOrdType = class(TType)
  end;

  TIntKind = (intS8, intU8, intS16, intU16, intS32, intU32, intS64, intU64);

  TIntType = class(TOrdType)
  protected
    function GetAlignSize: byte; override;
  public
    Kind: TIntKind;
    constructor Create; override;
  end;

  TBoolKind = (bolStd, bolByte, bolWord, bolLong);

  TBoolType = class(TOrdType)
  public
    Kind: TBoolKind;
    constructor Create; override;
  end;

  TCharKind = (charAnsi, charWide);

  TCharType = class(TOrdType)
  public
    Kind: TCharKind;
    constructor Create; override;
  end;

  TNumericKind = (numSingle, numDouble, numExtended, numCurrency, numComp, numReal48);

  TNumericType = class(TType)
  public
    Kind: TNumericKind;
    constructor Create; override;
  end;

  TStringKind = (strAnsi, strWide, strUnicode, strAShort, strWShort);

  TStringType = class(TType)
  private
    FKind: TStringKind;
    FCodePage: word;
    FCharCount: word;
  protected
    function GetAlignSize: byte; override;
  public
    constructor Create(AKind: TStringKind); reintroduce;
    procedure Update;
    property Kind: TStringKind read FKind write FKind;
    property CodePage: word read FCodePage write FCodePage;
    property CharCount: word read FCharCount write FCharCount;
  end;

  TVariantType = class(TType)
  protected
    function GetAlignSize: byte; override;
  public
    IsOle: boolean;
    constructor Create; override;
  end;

  TEnumType = class;

  TEnumValue = class(TSymbol)
  public
    EnumType: TEnumType;
    Value: integer;
    constructor Create; override;
  end;

  TSubrangeType = class;

  TEnumType = class(TType)
  private
    FHighValue, FLowValue: integer;
    procedure UpdateRange;
    procedure CalcSize(MinSize: integer = 1);
  public
    SubrangeType: TSubrangeType;
    Values: TFPList;
    MinEnumSize: byte;
    constructor Create; override;
    destructor Destroy; override;
    procedure Update;
    property LowValue: integer read FLowValue;
    property HighValue: integer read FHighValue;
  end;

  TSetType = class;

  TSubrangeType = class(TType)
  private
    FBaseType: TType;
    procedure SetBaseType(const Value: TType);
  public
    SetType: TSetType;
    RangeBegin, RangeEnd: int64;
    constructor Create; override;
    property BaseType: TType read FBaseType write SetBaseType;
    function SubSetOf(typ: TSubrangeType): boolean; {$IFNDEF DEBUG}inline;{$ENDIF}
  end;

  TSetType = class(TType)
  protected
    function GetAlignSize: byte; override;
    procedure UpdateSize;
  public
    RangeType: TSubrangeType;
    constructor Create; override;
    function IsCommonSetType: boolean;
    procedure Update;
  private
    FLowByte, FHighByte: byte;
  public
    property LowByte: byte read FLowByte;
    property HighByte: byte read FHighByte;
  end;

  TPointerType = class(TType)
  public
    RefType: TType;
    constructor Create; override;
    //destructor Destroy; override;
    function IsUntype: boolean;
  end;

  TStructAttribute = (staNeedInit, staNeedFree);
  TStructAttributes = set of TStructAttribute;

  TArrayType = class(TType)
  private
    function GetDimensionCount: integer;
    function GetElementCount: int64;
  protected
    function GetAlignSize: byte; override;
  public
    ElementType: TType;
    Range: TSubrangeType;
    IsPacked: boolean;
    ArrayAttr: TStructAttributes;
    constructor Create; override;
    procedure Update;
    property DimensionCount: integer read GetDimensionCount;
    property ElementCount: int64 read GetElementCount;
  end;

  TDynamicArrayType = class(TType)
  protected
    function GetAlignSize: byte; override;
  public
    ElementType: TType;
    IsPacked: boolean;
    constructor Create; override;
  end;

  TOpenArrayType = class(TType)
  protected
    function GetAlignSize: byte; override;
  public
    ElementType: TType;
    ElementCount: integer;
    constructor Create; override;
  end;

  TStructuredType = class(TType)
  end;

  TFieldAttribute = (faRecVar);
  TFieldAttributes = set of TFieldAttribute;

  TField = class(TSymbol)
  public
    FieldType: TType;
    Offset: cardinal;
    FieldAttr: TFieldAttributes;
    constructor Create; override;
    function AlignOfParent: byte;
  end;

  TPropertyAttribute = (paNoDefault, paNoStored, paDefaultProp);
  TPropertyAttributes = set of TPropertyAttribute;

  TMultiAccessor = class(TSymbol)
  public
    Fields: array of TSymbol;
    FieldCount: integer;
    constructor Create; override;
    procedure Add(Field: TSymbol); reintroduce;
    function Last: TField;
    function First: TSymbol;
  end;

  TProperty = class(TSymbol)
  public
    PropType: TType;
    Getter, Setter, Stored: TSymbol;
    Index: integer;
    Params: TFuncParamList;
    DefaultValue: TValueRec;
    PropAttr: TPropertyAttributes;
    constructor Create; override;
    destructor Destroy; override;
    procedure CreateParams;
    function ParamCount: integer;
    function HasIndexSpec: boolean;
    function GetterType: TType;
    function SetterType: TType;
  end;

  TMethod = class;
  TRecordVariant = class;

  TRecordBody = class
  private
    procedure UpdateAlign;
    function RecordSize: int64;
  public
    Members: TFPList;
    Selector: TField;
    Variants: TRecordVariant;
    MaxAlignSize: byte;
    constructor Create;
    destructor Destroy; override;
    procedure Update(GlobalAlignSize: byte; Offset: cardinal);
    procedure AddFields(Symbols: TSymbolTable);
  end;

  TRecordBodyClass = class of TRecordBody;

  TRecordVariant = class(TRecordBody)
  public
    Next: TRecordVariant;
    Offset: cardinal;
    destructor Destroy; override;
  end;

  TRecordType = class(TStructuredType)
  protected
    procedure UpdateAlign;
    function GetAlignSize: byte; override;
    procedure AddSymbol(Sym: TSymbol); override;
  public
    Symbols: TSymbolTable;
    Body: TRecordBody;
    GlobalAlignSize: byte;
    RecordAttr: TStructAttributes;
    constructor Create; override;
    destructor Destroy; override;
    function FindSymbol(const S: TSymString): TSymbol; {$IFNDEF DEBUG}inline;{$ENDIF}
    procedure Add(Sym: TSymbol); override;
    procedure Update;
  end;

  TClassRefType = class;
  TClassAttribute = (caSealed, caAbstract, caRtti);
  TClassAttributes = set of TClassAttribute;
  TMethodResolution = class;

  TIntfVmtEntry = record
    IntfMethod, ImplMethod: TMethod;
  end;
  TIntfVmtEntryArray = array of TIntfVmtEntry;

  TClassIntfEntry = class
  private
    FIntfType: TInterfaceType;
    FEntries: TIntfVmtEntryArray;
    FImplGetter: TMethod;
    FEntryCount: integer;
    FOffset: integer;
  public
    procedure UpdateVmtEntry(Index: integer; AIntfMeth, AImplMeth: TMethod);
    property EntryCount: integer read FEntryCount;
    property IntfType: TInterfaceType read FIntfType;
    property Entries: TIntfVmtEntryArray read FEntries;
    property Offset: integer read FOffset;
    property ImplGetter: TMethod read FImplGetter;
  end;

  TClassType = class(TStructuredType)
  private
    FClassRef: TClassRefType;
    FAllSymbols: TSymbolTable;
    FInterfaces: TFPList;
    function GetAllSymbols: TSymbolTable;
    function GetInterface(Index: integer): TInterfaceType;
    function GetInterfaceCount: integer;
    procedure CreateInterfaces;
    function GetIntfEntry(Index: integer): TClassIntfEntry;
  protected
    procedure AddSymbol(Sym: TSymbol); override;
  public
    Symbols: TSymbolTable;
    Base: TClassType;
    DefaultProp: TProperty;
    ObjectSize: int64;
    VmtEntryCount: integer;
    Vmt: array of TMethod;
    MR: TMethodResolution;
    GlobalAlignSize: byte;
    ClassAttr: TClassAttributes;
    constructor Create; override;
    destructor Destroy; override;
    property AllSymbols: TSymbolTable read GetAllSymbols;
    function RttiEnabled: boolean;
    function FindSymbol(const S: TSymString): TSymbol;
    function FindCurSymbol(const S: TSymString): TSymbol;
    function FindBaseSymbol(const S: TSymString): TSymbol;
    function IsInheritedFrom(ABase: TClassType): boolean;
    function IsImplemented(AIntf: TInterfaceType): boolean;
    function FindIntfEntry(AIntf: TInterfaceType): TClassIntfEntry;
    function GetClassRef: TClassRefType;
    procedure AddInterface(Intf: TInterfaceType);
    procedure ClearInterface;
    function GetInternalAddrOfIntf(i: integer): Pointer;
    procedure Update(PtrSize: integer);
    procedure Add(Sym: TSymbol); override;
    property Interfaces[Index: integer]: TInterfaceType read GetInterface;
    property IntfEntries[Index: integer]: TClassIntfEntry read GetIntfEntry;
    property InterfaceCount: integer read GetInterfaceCount;
  end;

  TClassRefType = class(TType)
  public
    RefType: TClassType;
    constructor Create; override;
    function IsInheritedFrom(ClassRef: TClassRefType): boolean;
  end;

  TIntfPropertyAttribute = (ipaNoUsed, ipaDefaultProp, ipaReadOnly, ipaWriteOnly, ipaHasDispID);
  TIntfPropertyAttributes = set of TIntfPropertyAttribute;

  TIntfProperty = class(TSymbol)
  public
    PropType: TType;
    Getter, Setter: TMethod;
    Params: TFuncParamList;
    DispID: integer;
    PropAttr: TIntfPropertyAttributes;
    constructor Create; override;
    destructor Destroy; override;
    procedure CreateParams;
    function ParamCount: integer;
  end;

  TInterfaceType = class(TType)
  private
    FAllSymbols: TSymbolTable;
    function GetAllSymbols: TSymbolTable;
  protected
    procedure AddSymbol(Sym: TSymbol); override;
  public
    Guid: TGuid;
    Symbols: TSymbolTable;
    Base: TInterfaceType;
    DefaultProp: TIntfProperty;
    VmtEntryCount: word;
    IsDisp: boolean;
    constructor Create; override;
    destructor Destroy; override;
    property AllSymbols: TSymbolTable read GetAllSymbols;
    function FindSymbol(const S: TSymString): TSymbol;
    function FindCurSymbol(const S: TSymString): TSymbol;
    function FindBaseSymbol(const S: TSymString): TSymbol;
    function IsInheritedFrom(ABase: TInterfaceType): boolean;
    procedure Add(Sym: TSymbol); override;
    procedure UpdateVmt;
  end;

  TObjectAttribute = (oaHasVirtual, oaHasVmt, oaBeginVmt);
  TObjectAttributes = set of TObjectAttribute;

  TObjectType = class(TType)
  private
    FAllSymbols: TSymbolTable;
    function GetAllSymbols: TSymbolTable;
  protected
    procedure AddSymbol(Sym: TSymbol); override;
  public
    Symbols: TSymbolTable;
    Base: TObjectType;
    DefaultProp: TProperty;
    VmtOffset: cardinal;
    VmtEntryCount: integer;
    GlobalAlignSize: byte;
    ObjectAttr: TObjectAttributes;
    constructor Create; override;
    destructor Destroy; override;
    property AllSymbols: TSymbolTable read GetAllSymbols;
    function FindSymbol(const S: TSymString): TSymbol;
    function FindCurSymbol(const S: TSymString): TSymbol;
    function FindBaseSymbol(const S: TSymString): TSymbol;
    function IsInheritedFrom(ABase: TObjectType): boolean;
    procedure Update(PtrSize: integer);
    procedure Add(Sym: TSymbol); override;
  end;

  TFileType = class(TType)
  public
    ElementType: TType;
    constructor Create; override;
    function IsUntype: boolean;
  end;

  TTextType = class(TType)
  public
    constructor Create; override;
  end;

  TSymbolType = class(TType)
  public
    Reference: TSymbol;
    constructor Create; override;
  end;

  TArgumentModifier = (argDefault, argConst, argVar, argOut);
  TArgState = (asInit, asNestRef, asByRef, asStructRef, asStructValue, asNeedAddRef, asNeedFree);
  TArgStates = set of TArgState;
  TArgumentKind = (akNormal, akArrayOfType, akArrayOfConst, akUntype);

  TFuncParam = class(TSymbol)
  public
    ParamType: TType;
    ArgKind: TArgumentKind;
    States: TArgStates;
    Modifier: TArgumentModifier;
    Level: byte;
    Index: word;
    DefaultValue: TValueRec;
    constructor Create; override;
    destructor Destroy; override;
    function IsReadOnly: boolean;
  end;

  TFuncParamList = class
  private
    FItems: array of TFuncParam;
    FCount: integer;
    function Get(Index: integer): TFuncParam;
    function GetCapacity: integer;
    procedure SetCapacity(Value: integer);
    procedure SetCount(Value: integer);
  public
    property Capacity: integer read GetCapacity write SetCapacity;
    property Count: integer read FCount write SetCount;
    property Items[Index: integer]: TFuncParam read Get; default;
    procedure Add(P: TFuncParam);
    procedure Copy(Source: TFuncParamList);
  end;

  TMethodKind = (mkNormal, mkConstructor, mkDestructor, mkObjCtor, mkObjDtor, mkRecCtor, mkRecDtor);
  TObjectKind = (okClass, okObject, okRecord);

  TProceduralType = class(TType)
  public
    Params: TFuncParamList;
    ReturnType: TType;
    CallConvention: TCallingConvention;
    IsMethodPointer: boolean;
    MethodKind: TMethodKind;
    ObjectKind: TObjectKind;
    constructor Create; override;
    destructor Destroy; override;
    procedure CreateParams;
    function ParamCount: integer;
    function MinOfParams: integer;
  end;

  TCompilerDirective = (cdBoolEval, cdIOChecks, cdOverflowChecks, cdRangeChecks, cdSafeDivide,
    cdTypeInfo, cdTypedAddress, cdWriteableConst, cdAssertions, cdOptimization, cdStackFrames,
    cdDebugInfo, csExtendedSyntax, csLongStrings, csOpenStrings, csVarStringChecks, csRealCompatibility,
    cdAlign, cdAppType, cdMinEnumSize, cdDefine, cdUndef, cdIf, cdIfOpt, cdIfDef, cdIfNDef, cdElse,
    cdElseIf, cdEndIf, cdIfEnd, cdNoDefine, cdHPPEmit, cdExternalSym, cdResource, cdInclude, cdMode, cdModeSwitch);
  TCodeSwitches = set of cdBoolEval..cdSafeDivide;
  TExprOpCode = (opNONE, opNE, opEQ, opLT, opLE, opGT, opGE, opIN, opIS, opAS, opADD, opSUB,
    opOR, opXOR, opMUL, opFDIV, opIDIV, opMOD, opAND, opSHL, opSHR, opMEMBER, opCAST, opCALL,
    opRANGE, opINDEX, opASSIGN, opFMT, opNOT, opNEG, opPOS, opINHERITED, opSET, opLIST, opADDR,
    opDBLADDR, opINST, opDISPCALL, opNIL, opCONST, opSYMBOL);
  TExprOpKind = (opkNone, opkUnary, opkBinary, opkList, opkConst, opkSymbol);
  TExprAttribute = (eaVerified, eaInvalid, eaDelayed, eaCall, eaArgList, eaOverloadRestrict,
    eaArrayProp, eaInherited, eaConst, eaVarCast, eaStrOp, eaVarOp, eaSetOp, eaRes2, eaRes3, eaRes4);
  TExprAttributes = set of TExprAttribute;

  TExpr = class(TAstNode)
  private
    FTyp: TType;
    FParent: TExpr;
    FOpCode: TExprOpCode;
  public
    Switches: TCodeSwitches;
    Attr: TExprAttributes;
    property Typ: TType read FTyp write FTyp;
    property OpCode: TExprOpCode read FOpCode write FOpCode;
    property Parent: TExpr read FParent;
    constructor Create; override;
    procedure Reset; virtual;
    procedure Remove(Child: TExpr); virtual;
    procedure Detach;
    function GetReference: TSymbol;
    function GetFunctionSymbol: TFunctionDecl;
    function GetVariableSymbol: TVariable;
    function GetConstantSymbol: TConstant;
    procedure SetReference(Ref: TSymbol);
    function IsTypeSymbol: boolean;
    function IsTypedConstant: boolean;
    function IsConstantValue: boolean;
    function IsStringConstant: boolean;
    function IsCharConstant: boolean;
    function IsEmptyString: boolean;
    function HasMemory: boolean;
    function IsFunction: boolean;
    function IsCtorSymbol: boolean;
    function IsClassType: boolean;
    function IsCtorCall: boolean;
    function IsNilConst: boolean;
  end;

  TExprClass = class of TExpr;

  TUnaryExpr = class(TExpr)
  private
    fOperand: TExpr;
    procedure SetOperand(const Value: TExpr);
  public
    property Operand: TExpr read fOperand write SetOperand;
    procedure Reset; override;
    procedure Remove(Child: TExpr); override;
  end;

  TBinaryExpr = class(TExpr)
  private
    FLeft: TExpr;
    FRight: TExpr;
    procedure SetLeft(const Value: TExpr);
    procedure SetRight(const Value: TExpr);
  public
    property Left: TExpr read FLeft write SetLeft;
    property Right: TExpr read FRight write SetRight;
    procedure Reset; override;
    procedure Remove(Child: TExpr); override;
  end;

  TListExpr = class(TExpr)
  public
    Items: array of TExpr;
    Count: integer;
    constructor Create; override;
    procedure Reset; override;
    procedure Add(E: TExpr);
    procedure Insert(Index: integer; E: TExpr);
    procedure Delete(Index: integer);
    procedure Remove(E: TExpr); override;
    function IndexOf(E: TExpr): integer;
    procedure Replace(Index: integer; E: TExpr);
    procedure SetCapacity(Num: integer);
  end;

  TSymbolExpr = class(TExpr)
  public
    Name: TSymString;
    Reference: TSymbol;
    procedure Reset; override;
  end;

  TConstExpr = class(TExpr)
  public
    Value: TValueRec;
    destructor Destroy; override;
    procedure Reset; override;
  end;

  TStrConstExpr = class(TExpr)
  public
    RawValue: string;
    procedure Reset; override;
  end;

  TVarAttribute = (vaReserved1, vaReserved2, vaReadOnly, vaLocal, vaHidden, vaTls, vaResult, vaSelf);
  TVarAttributes = set of TVarAttribute;
  TVarState = (vsInit, vsNestRef, vsResultAddr, vsNeedInit, vsNeedFree, vsTemp);
  TVarStates = set of TVarState;

  TVariable = class(TSymbol)
  public
    VarType: TType;
    Value: TValueRec;
    AbsVar: TSymbol;
    VarAttr: TVarAttributes;
    States: TVarStates;
    Level: byte;
    Index: word;
    constructor Create; override;
    destructor Destroy; override;
  end;

  TConstant = class(TSymbol)
  public
    ConstType: TType;
    Value: TValueRec;
    IsResStr: boolean;
    constructor Create; override;
    destructor Destroy; override;
  end;

  TFunctionModifier = (fmVirtual, fmDynamic, fmAbstract, fmOverride, fmOverload, fmMessage,
    fmReintroduce, fmStatic, fmInline, fmAssembler, fmVarargs, fmLocal, fmDispID, fmExport, fmNear,
    fmFar, fmExternal, fmForward, fmNoReturn, fmOvrldFlag);
  TFunctionModifiers = set of TFunctionModifier;

  TFunctionDecl = class(TSymbol)
  private
    FProcType: TProceduralType;
    function GetProceduralType: TProceduralType;
  protected
    procedure CreateProceduralType; virtual;
  public
    ID: integer;
    Params: TFuncParamList;
    ReturnType: TType;
    NextOverload: TFunctionDecl;
    Modifiers: TFunctionModifiers;
    CallConvention: TCallingConvention;
    Level: byte;
    destructor Destroy; override;
    procedure CreateParams;
    function ParamCount: integer;
    function MinOfParams: integer;
    function IsOverload: boolean;
    procedure AddOverload(Func: TFunctionDecl);
    property ProceduralType: TProceduralType read GetProceduralType;
  end;

  TExternalFunction = class(TFunctionDecl)
  public
    FileName: string;
    RoutineName: TSymString;
    RoutineNo: integer;
    constructor Create; override;
  end;

  TFuncAttr = (faNeedFP, faNeedFPArg, faOperatorOverloading);
  TFuncAttrs = set of TFuncAttr;

  TFunction = class(TFunctionDecl)
  protected
    procedure AddSymbol(Sym: TSymbol); override;
  public
    LocalSymbols: TSymbolTable;
    StartStmt: TCompoundStmt;
    Codes: TObject;
    FuncAttr: TFuncAttrs;
    constructor Create; override;
    destructor Destroy; override;
    procedure Add(Sym: TSymbol); override;
  end;

  TMethod = class
    (TFunction)
  protected
    procedure CreateProceduralType; override;
  public
    MethodKind: TMethodKind;
    ObjectKind: TObjectKind;
    VTIndex: smallint;
    MsgNo: word;
    DispID: integer;
    constructor Create; override;
    function IsClassOrStatic: boolean;
  end;

  TMethodResolution = class(TSymbol)
  public
    ImplementingMethod: TMethod;
    InterfaceMethod: TMethod;
    constructor Create; override;
  end;

  TBuiltinFunctionKind = (bfAbs, bfAddr, bfAssigned, bfBreak, bfChr, bfContinue, bfCopy, bfDec,
    bfDispose, bfExclude, bfExit, bfFinalize, bfFreeMem, bfGetMem, bfHi, bfHigh, bfInc, bfInclude,
    bfInitialize, bfLength, bfLo, bfLow, bfNew, bfOdd, bfOrd, bfPred, bfPtr, bfRound, bfSucc,
    bfSetLength, bfSizeOf, bfSwap, bfTrunc, bfTypeInfo, bfNoop, bfStr, bfWrite, bfWriteLn, bfRead, bfReadLn);

  TBuiltinFunction = class(TSymbol)
  public
    Kind: TBuiltinFunctionKind;
    constructor Create; override;
  end;

  TStmtKind = (skEmptyStmt, skCompoundStmt, skIfStmt, skCaseStmt, skForStmt, skWhileStmt,
    skRepeatStmt, skTryStmt, skLabelStmt, skRaiseStmt, skAssignmentStmt, skCallStmt, skGotoStmt,
    skCtorInit, skCtorAfter, skDtorBefore, skDtorInit, skCleanup, skHandleExcept, skLocalInit,
    skLocalUninit, skJumpTrue, skJumpFalse, skJump, skMark, skOAInit);
  TStmtAttribute = (stmtNoReturn, stmtUnreachable, stmtBreak, stmtContinue, stmtExit);
  TStmtAttributes = set
    of TStmtAttribute;

  TStatement = class(TAstNode)
  private
    FStmtKind: TStmtKind;
  public
    Parent: TStatement;
    Data: Pointer;
    Attr: TStmtAttributes;
    property StmtKind: TStmtKind read FStmtKind;
  end;

  TStatementClass = class of TStatement;

  TEmptyStmt = class(TStatement)
  public
    constructor Create; override;
  end;

  TCompoundStmt = class(TStatement)
  public
    Statements: TFPList;
    IncludeBegin: boolean;
    constructor Create; override;
    destructor Destroy; override;
  end;

  TCallStmt = class(TStatement)
  public
    CallExpr: TExpr;
    constructor Create; override;
  end;

  TLabeledStmt = class(TStatement)
  public
    LabelSym: TStmtLabel;
    constructor Create; override;
  end;

  TStmtLabel = class(TSymbol)
  public
    Stmt: TLabeledStmt;
    constructor Create; override;
  end;

  TAssignmentStmt = class(TStatement)
  public
    Left, Right: TExpr;
    constructor Create; override;
  end;

  TIfStmt = class(TStatement)
  public
    Value: TExpr;
    TrueStmt: TStatement;
    FalseStmt: TStatement;
    constructor Create; override;
  end;

  TForStmt = class(TStatement)
  public
    Value: TSymbol;
    Down: boolean;
    Start: TExpr;
    Stop: TExpr;
    Stmt: TStatement;
    constructor Create; override;
  end;

  TGotoStmt = class(TStatement)
  public
    StmtLabel: TStmtLabel;
    constructor Create; override;
  end;

  TWhileStmt = class(TStatement)
  public
    Condition: TExpr;
    Stmt: TStatement;
    constructor Create; override;
  end;

  TCaseRange = record
    Start, Stop: int64;
    Coord: TAstNodeCoord;
  end;

  TCaseSelector = class
  private
    FCount: integer;
  public
    Values: array of TCaseRange;
    Stmt: TStatement;
    destructor Destroy; override;
    procedure AddRange(Start, Stop: int64);
    function Contains(Start, Stop: int64): boolean;
    function TotalValueCount: int64;
    procedure Clear;
    property Count: integer read FCount;
  end;

  TCaseStmt = class(TStatement)
  private
    FCount: integer;
  public
    Expr: TExpr;
    Selectors: array of TCaseSelector;
    Default: TCompoundStmt;
    constructor Create; override;
    destructor Destroy; override;
    property Count: integer read FCount;
    procedure AddSelector(Selector: TCaseSelector);
    procedure Clear;
    function Contains(Start, Stop: int64): boolean;
    function TotalValueCount: int64;
  end;

  TRepeatStmt = class(TStatement)
  public
    Condition: TExpr;
    Stmt: TCompoundStmt;
    constructor Create; override;
  end;

  TExceptHandler = class
  public
    ExceptVar: TVariable;
    Stmt: TStatement;
  end;

  TExceptBlock = class
  private
    FCount: integer;
  public
    ExceptHandlers: array of TExceptHandler;
    Default: TCompoundStmt;
    destructor Destroy; override;
    procedure AddExceptHandler(Block: TExceptHandler);
    procedure Clear;
    property Count: integer read FCount;
  end;

  TTryStmt = class(TStatement)
  public
    Stmt: TCompoundStmt;
    FinallyStmt: TCompoundStmt;
    ExceptBlock: TExceptBlock;
    constructor Create; override;
    destructor Destroy; override;
    function IsFinallyOrExcept(S: TStatement): boolean;
  end;

  TRaiseStmt = class(TStatement)
  public
    Expr: TExpr;
    constructor Create; override;
  end;

  TSymbolPosition = THashTablePosition;

  TSymbolTable = class(TCustomHashTable)
  private
    FOwner: TSymbol;
    FAutoAddToOwner: boolean;
    function GetSymbol(Index: integer): TSymbol;
  public
    constructor Create(AOwner: TSymbol);
    function GetStart(const S: TSymString): TSymbolPosition;
    function GetNext(var Pos: TSymbolPosition): TSymbol;
    function Find(const S: TSymString): TSymbol; overload;
    function Find(M: TModule; const S: TSymString): TSymbol; overload;
    function Add(Sym: TSymbol): boolean;
    function AddOvrld(Sym: TFunctionDecl): boolean;
    procedure Clear(FreeSym: boolean = False);
    property Item[Index: integer]: TSymbol read GetSymbol; default;
    property Owner: TSymbol read FOwner;
    property AutoAddToOwner: boolean read FAutoAddToOwner write FAutoAddToOwner;
  end;

  TDirectiveIdent = (idNone, idDeprecated, idLibrary, idPlatform, idExperimental, idUnimplemented,
    idRegister, idPascal, idCDecl, idStdCall, idSafeCall, idVirtual, idDynamic, idAbstract,
    idOverride, idOverload, idMessage, idReintroduce, idStatic, idInline, idAssembler, idVarargs,
    idLocal, idDispMId, idExport, idNear, idFar, idExternal, idForward);
  TDirectiveIdents = set of TDirectiveIdent;

function FindDirective(const S: TSymString): TDirectiveIdent;

const
  OpKinds: array[TExprOpCode] of TExprOpKind =
    (opkNone, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary,
    opkBinary, opkBinary, opkBinary, opkBinary,
    opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary,
    opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkBinary, opkUnary, opkUnary,
    opkUnary, opkUnary, opkUnary, opkList, opkUnary, opkUnary, opkUnary, opkUnary, opkConst, opkConst,
    opkSymbol);
  ExprKinds: array[TExprOpCode] of shortint =
    (0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1,
    1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4);
  TypeNames: array[TTypeCode] of
    string = ('unknown', 'untype', 'Integer', 'Real', 'Boolean', 'Char', 'Pointer', 'PAnsiChar',
    'PWideChar', 'String', 'Variant', 'file', 'Text', 'procedural', 'record', 'object', 'class',
    'interface', 'classref', 'enum', 'set', 'subrange', 'array', 'dynamicarray', 'unitscope',
    'alias', 'clonetype', 'openarray', 'vector');
  IntTypeNames: array[TIntKind] of string =
    ('Shortint', 'Byte', 'Smallint', 'Word', 'Longint', 'LongWord', 'Int64', 'UInt64');
  NumericTypeNames: array[TNumericKind] of string = ('Single', 'Double', 'Extended', 'Currency', 'Comp', 'Real48');
  BoolTypeNames: array[TBoolKind] of string = ('Boolean', 'ByteBool', 'WordBool', 'LongBool');
  CharTypeNames: array[TCharKind] of string = ('AnsiChar', 'WideChar');
  StringTypeNames: array[TStringKind] of string =
    ('AnsiString', 'WideString', 'UnicodeString', 'ShortString', 'WShortString');
  AutoInitTypes = [typString, typVariant, typInterface, typDynamicArray];
  AutoFreeTypes = [typString, typVariant, typInterface, typDynamicArray];

procedure ValClear(var V: TValueRec);
procedure ValInit(out V: TValueRec);
function ValFromBool(B: boolean): TValueRec; overload;
function ValFromBool(I: cardinal): TValueRec; overload;
function ValFromChar(C: AnsiChar): TValueRec; overload;
function ValFromWChar(C: widechar): TValueRec; overload;
function ValFromInt(I: integer): TValueRec; overload;
function ValFromInt(I: int64): TValueRec; overload;
function ValFromCurr(I: currency): TValueRec; overload;
function ValFromReal(R: real): TValueRec; overload;
function ValFromStr(const S: UTF8String): TValueRec; overload;
function ValFromWStr(const S: WideString): TValueRec; overload;
function ValFromSet(S: TSetValue): TValueRec; overload;
function ValFromPtr(P: Pointer): TValueRec; overload;
function ValFromSymbol(Sym: TSymbol): TValueRec; overload;
procedure ValFromBool(var V: TValueRec; B: boolean); overload;
procedure ValFromChar(var V: TValueRec; C: AnsiChar); overload;
procedure ValFromWChar(var V: TValueRec; C: widechar); overload;
procedure ValFromInt(var V: TValueRec; I: integer); overload;
procedure ValFromInt(var V: TValueRec; I: int64); overload;
procedure ValFromCurr(var V: TValueRec; I: currency); overload;
procedure ValFromReal(var V: TValueRec; R: real); overload;
procedure ValFromRawStr(var V: TValueRec; const S: ansistring); overload;
procedure ValFromStr(var V: TValueRec; const S: UTF8String); overload;
procedure ValFromWStr(var V: TValueRec; const S: WideString); overload;
procedure ValFromSet(var V: TValueRec; S: TSetValue); overload;
procedure ValFromArray(var V: TValueRec; Arr: TArrayValue); overload;
procedure ValFromPtr(var V: TValueRec; P: Pointer); overload;
procedure ValFromSymbol(var V: TValueRec; Sym: TSymbol); overload;
procedure ValFromAddrOffset(var V: TValueRec; Sym: TSymbol; Offset: integer);
procedure ValFromIID(var V: TValueRec; Intf: TInterfaceType);
procedure ValDefault(var V: TValueRec; typ: TType);
function ValIsClear(const V: TValueRec): boolean;
procedure ValCopy(var Dest: TValueRec; const Source: TValueRec); overload;
function ValCopy(const Source: TValueRec): TValueRec; overload;
function ValCast(const V: TValueRec; vt: TValueType): TValueRec;
function ValToInt(const V: TValueRec): integer;
function ValToInt64(const V: TValueRec): int64;
function ValToBool(const V: TValueRec): boolean;
function ValToReal(const V: TValueRec): real;
function ValToCurr(const V: TValueRec): currency;
function ValToRawStr(const V: TValueRec): ansistring;
function ValToStr(const V: TValueRec): UTF8String;
function ValToWStr(const V: TValueRec): WideString;
function ValToSet(const V: TValueRec): TSetValue;
function ValToPtr(const V: TValueRec): Pointer;
function ValGetAddrOffset(const V: TValueRec; out Sym: TSymbol): Integer;
function ValToVar(const V: TValueRec): variant;
function ValOp(const v1, v2: TValueRec; op: TExprOpCode): TValueRec;
function ValCmp(const v1, v2: TValueRec; op: TExprOpCode): TValueRec;
function ValIn(const v1, v2: TValueRec): TValueRec;
function ValNot(const v1: TValueRec): TValueRec;
function ValNeg(const v1: TValueRec): TValueRec;
function ValAbs(const V: TValueRec): TValueRec;
function ValHi(const V: TValueRec; typ: TIntType): TValueRec;
function ValLo(const V: TValueRec; typ: TIntType): TValueRec;
function ValChr(const V: TValueRec): TValueRec;
function ValOdd(const V: TValueRec): TValueRec;
function ValOrd(const V: TValueRec): TValueRec;
function ValPred(const V: TValueRec): TValueRec;
function ValRound(const V: TValueRec): TValueRec;
function ValSucc(const V: TValueRec): TValueRec;
function ValSwap(const V: TValueRec; typ: TIntType): TValueRec;
function ValTrunc(const V: TValueRec): TValueRec;
function ValIsCompatible(const V: TValueRec; typ: TType): boolean;
function TypIsVariantCompatible(typ: TType): boolean;
function TypIsVariantArithCompatible(typ: TType): boolean;
function TypIsStringArithCompatible(typ: TType): boolean;

implementation

uses Math, err;

procedure ValCastErr;
begin
  raise Exception.Create('value cast error');
end;

procedure ValOpErr;
begin
  raise Exception.Create('Invalid operator and operand');
end;

procedure ValFuncErr;
begin
  raise Exception.Create('Invalid function on value');
end;

procedure ValClear(var V: TValueRec);
begin
  case V.VT of
    vtStr: string(V.VStr) := '';
    vtWStr: string(V.VWStr) := '';
    vtSet: TSetValue(V.VSet).Free;
    vtArray: TArrayValue(V.VSet).Free;
    vtRecord: TRecordValue(V.VSet).Free;
  end;
  V.VT := vtEmpty;
end;

procedure ValInit(out V: TValueRec);
begin
  V.VT := vtEmpty;
end;

function ValFromBool(B: boolean): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtBool;
  Result.VBool := Ord(B);
end;

function ValFromBool(I: cardinal): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtBool;
  Result.VBool := I;
end;

function ValFromChar(C: AnsiChar): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtAChr;
  Result.VAChr := C;
end;

function ValFromWChar(C: widechar): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtWChr;
  Result.VWChr := word(C);
end;

function ValFromInt(I: integer): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtInt;
  Result.VInt := I;
end;

function ValFromInt(I: int64): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtInt64;
  Result.VInt64 := I;
end;

function ValFromCurr(I: currency): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtCurr;
  Result.VCurr := I;
end;

function ValFromReal(R: real): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtReal;
  Result.VReal := R;
end;

function ValFromStr(const S: UTF8String): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtStr;
  Result.VStr := nil;
  UTF8String(Result.VStr) := S;
end;

function ValFromWStr(const S: WideString): TValueRec;
begin
  Result := ValFromStr(Utf8Encode(S));
end;

function ValFromSet(S: TSetValue): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtSet;
  Result.VSet := S;
end;

function ValFromPtr(P: Pointer): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtPtr;
  Result.VPtr := P;
end;

function ValFromSymbol(Sym: TSymbol): TValueRec;
begin
  ValInit(Result);
  Result.VT := vtSymbol;
  Result.VSymbol := Sym;
end;

procedure ValFromBool(var V: TValueRec; B: boolean);
begin
  ValClear(V);
  V.VT := vtBool;
  V.VBool := Ord(B);
end;

procedure ValFromChar(var V: TValueRec; C: AnsiChar);
begin
  ValClear(V);
  V.VT := vtAChr;
  V.VAChr := C;
end;

procedure ValFromWChar(var V: TValueRec; C: widechar);
begin
  ValClear(V);
  V.VT := vtWChr;
  V.VWChr :=
    word(C);
end;

procedure ValFromInt(var V: TValueRec; I: integer);
begin
  ValClear(V);
  V.VT := vtInt;
  V.VInt := I;
end;

procedure ValFromInt(var V: TValueRec; I: int64);
begin
  ValClear(V);
  V.VT := vtInt64;
  V.VInt64 := I;
end;

procedure ValFromCurr(var V: TValueRec; I: currency);
begin
  ValClear(V);
  V.VT := vtCurr;
  V.VCurr := I;
end;

procedure ValFromReal(var V: TValueRec; R: real);
begin
  ValClear(V);
  V.VT := vtReal;
  V.VReal := R;
end;

procedure ValFromRawStr(var V: TValueRec; const S: ansistring); overload;
begin
  ValFromStr(V, Utf8Encode(S));
end;

procedure ValFromStr(var V: TValueRec; const S: UTF8String);
begin
  ValClear(V);
  V.VT := vtStr;
  V.VStr := nil;
  UTF8String(V.VStr) := S;
end;

procedure ValFromWStr(var V: TValueRec; const S: WideString);
begin
  ValFromStr(V, Utf8Encode(S));
end;

procedure ValFromSet(var V: TValueRec; S: TSetValue);
begin
  ValClear(V);
  V.VT := vtSet;
  V.VSet := S;
end;

procedure ValFromArray(var V: TValueRec; Arr: TArrayValue);
begin
  ValClear(V);
  V.VT := vtArray;
  V.VArray := Arr;
end;

procedure ValFromPtr(var V: TValueRec; P: Pointer);
begin
  ValClear(V);
  V.VT := vtPtr;
  V.VPtr := P;
end;

procedure ValFromSymbol(var V: TValueRec; Sym: TSymbol);
begin
  ValClear(V);
  V.VT := vtSymbol;
  V.VSymbol := Sym;
end;

procedure ValFromAddrOffset(var V: TValueRec; Sym: TSymbol; Offset: integer);
begin
  ValClear(V);
  V.VT := vtAddrOffset;
  V.VSymbol := Sym;
  V.Res1 := Offset and $ffff;
  V.Res2 := (Offset shr 16) and $ffff;
end;

procedure ValFromIID(var V: TValueRec; Intf: TInterfaceType);
begin
  ValClear(V);
  V.VT := vtIID;
  V.VIID := Intf;
end;

procedure ValDefault(var V: TValueRec; typ: TType);
begin
  case typ.TypeCode of
    typInt, typEnum, typSubrange: ValFromInt(V, 1);
    typNumeric: ValFromReal(V, 1);
    typBool: ValFromBool(V, True);
    typChar: ValFromChar(V, #32);
    typPointer, typPAnsiChar, typPWideChar: ValFromPtr(V, nil);
    typString: ValFromStr(V, '');
    else
      ValFromPtr(V, nil);
  end;
end;

function ValIsClear(const V: TValueRec): boolean;
begin
  Result := V.VT = vtEmpty;
end;

procedure ValCopy(var Dest: TValueRec; const Source: TValueRec);
begin
  ValClear(Dest);
  case Source.VT of
    vtStr, vtWStr:
    begin
      Dest.VT := Source.VT;
      Dest.VStr := nil;
      ansistring(Dest.VStr) := ansistring(Source.VStr);
    end;
    vtSet: if Source.VSet <> nil then
      begin
        Dest.VT := Source.VT;
        Dest.VSet := TSetValue.Create;
        TSetValue(Dest.VSet).Assign(TSetValue(Source.VSet));
      end
      else
      begin
        Dest.VT := Source.VT;
        Dest.VSet := nil;
      end;
    vtArray:
    begin
      Dest.VT := Source.VT;
      Dest.VArray := TArrayValue.Create;
      Dest.VArray.Assign(Source.VArray);
    end;
    vtRecord:
    begin
      Dest.VT := Source.VT;
      Dest.VRecord := TRecordValue.Create;
      Dest.VRecord.Assign(Source.VRecord);
    end;
    else
      Move(Source, Dest, SizeOf(Dest));
  end;
end;

function ValCopy(const Source: TValueRec): TValueRec;
begin
  ValInit(Result);
  ValCopy(Result, Source);
end;

function ValCast(const V: TValueRec; vt: TValueType): TValueRec;
begin
  case vt of
    vtInt: Result := ValFromInt(ValToInt(V));
    vtInt64: Result := ValFromInt(ValToInt64(V));
    vtReal: Result := ValFromReal(ValToReal(V));
    vtCurr: Result := ValFromCurr(ValToCurr(V));
    vtBool: case V.VT of
        vtBool: Result := ValFromBool(ValToBool(V));
        vtInt: Result := ValFromBool(cardinal(V.VInt));
        vtInt64: Result := ValFromBool(cardinal(V.VInt64));
      end;
    vtPtr: Result := ValFromPtr(ValToPtr(V));
    else
  end;
end;

function ValToInt(const V: TValueRec): integer;
begin
  Result := ValToInt64(V);
end;

function ValToInt64(const V: TValueRec): int64;
begin
  case V.VT of
    vtInt: Result := V.VInt;
    vtInt64: Result := V.VInt64;
    vtBool: Result := Ord(V.VBool);
    vtAChr: Result := Ord(V.VAChr);
    vtWChr: Result := word(V.VWChr);
    else
      ValCastErr;
      Result := 0;
  end;
end;

function ValToBool(const V: TValueRec): boolean;
begin
  case V.VT of
    vtBool: Result := V.VBool <> 0;
    vtInt: Result := V.VInt <> 0;
    vtInt64: Result := V.VInt64 <> 0;
    vtReal: Result := V.VReal <> 0;
    vtCurr: Result := V.VCurr <> 0;
    else
      ValCastErr;
      Result := False;
  end;
end;

function ValToReal(const V: TValueRec): real;
begin
  case V.VT
    of
    vtInt: Result := V.VInt;
    vtInt64: Result := V.VInt64;
    vtReal: Result := V.VReal;
    vtCurr: Result := V.VCurr;
    else
      ValCastErr;
      Result := 0;
  end;
end;

function ValToCurr(const V: TValueRec): currency;
begin
  case V.VT of
    vtInt: Result := V.VInt;
    vtInt64: Result := V.VInt64;
    vtReal: Result := V.VReal;
    vtCurr: Result := V.VCurr;
    else
      ValCastErr;
      Result := 0;
  end;
end;

function ValToRawStr(const V: TValueRec): ansistring;
begin
  case V.VT of
    vtStr, vtWStr: Result := Utf8String(V.VStr);
    vtAChr: Result := V.VAChr;
    vtWChr: Result := UTF8String(UTF8Encode(WideChar(V.VWChr)));
    else
      Result := ValToStr(V);
  end;
end;

function ValToStr(const V: TValueRec): UTF8String;

  function WChar2Utf8Str(W: widechar): UTF8String;
  begin
    Result := Utf8Encode(WideString(W));
  end;

begin
  case V.VT of
    vtStr, vtWStr: Result := UTF8String(V.VStr);
    vtAChr: Result := V.VAChr;
    vtWChr: Result := WChar2Utf8Str(widechar(V.VWChr));
    vtInt: Result := IntToStr(V.VInt);
    vtInt64: Result := IntToStr(V.VInt64);
    vtReal: Result := FloatToStr(V.VReal);
    vtCurr: Result := CurrToStr(V.VCurr);
    vtBool: Result := BoolToStr(V.VBool <> 0);
    vtPtr: Result := Format('$%p', [V.VPtr]);
    vtSymbol: if V.VSymbol <> nil then
        Result := V.VSymbol.Name
      else
        Result := '';
    else
      ValCastErr;
      Result := '';
  end;
end;

function ValToWStr(const V: TValueRec): WideString;
begin
  case V.VT of
    vtStr, vtWStr: Result := UTF8Decode(UTF8String(V.VStr));
    vtAChr: Result := WideChar(V.VAChr);
    vtWChr: Result := widechar(V.VWChr);
    vtInt: Result := UTF8Decode(IntToStr(V.VInt));
    vtInt64: Result := UTF8Decode(IntToStr(V.VInt64));
    vtReal: Result := UTF8Decode(FloatToStr(V.VReal));
    vtCurr: Result := UTF8Decode(CurrToStr(V.VCurr));
    vtBool: Result := UTF8Decode(BoolToStr(V.VBool <> 0));
    vtPtr: Result := WideFormat('$%p', [V.VPtr]);
    vtSymbol: if V.VSymbol <> nil then
        Result := UTF8Decode(V.VSymbol.Name)
      else
        Result := '';
    else
      ValCastErr;
      Result := '';
  end;
end;

function ValToSet(const V: TValueRec): TSetValue;
begin
  case V.VT of
    vtSet: Result := TSetValue(V.VSet);
    vtEmpty: Result := nil;
    else
    begin
      ValCastErr;
      Result := nil;
    end;
  end;
end;

{$push}
{$warn 4055 off}
function ValToPtr(const V: TValueRec): Pointer;
begin
  case V.VT of
    vtInt: Result := Pointer(Int64(V.VInt));
    vtInt64: Result := Pointer(V.VInt64);
    vtStr, vtWStr: Result := V.VStr;
    vtPtr: Result := V.VPtr;
    vtSet: Result := TSetValue(V.VSet);
    vtSymbol: Result := V.VSymbol;
    vtEmpty: Result := nil;
    else
      ValCastErr;
      Result := nil;
  end;
end;
{$pop}

function ValGetAddrOffset(const V: TValueRec; out Sym: TSymbol): integer;
begin
  Result := 0;
  case V.VT of
    vtSymbol: Sym := V.VSymbol;
    vtAddrOfSymbol: Sym := V.VAddr;
    vtAddrOffset:
    begin
      Sym := V.VSymbol;
      Result := V.Res1 or (V.Res2 shl 16);
    end;
  end;
end;

function ValToVar(const V: TValueRec): variant;
begin
{$ifdef fpc}
  Result := Null;
{$endif}
end;

type
  TBaseType = (btErr, btEmp, btInt, btI64, btFlt, btCur, btSet, btStr, btBol);

function ValOp(const v1, v2: TValueRec; op: TExprOpCode): TValueRec;

  function IntOp(const Left, Right: TValueRec; Op: TExprOpCode): TValueRec;
  var
    L, R: integer;
  begin
    L := ValToInt(Left);
    R := ValToInt(Right);
    case Op of
      opADD: Result := ValFromInt(L + R);
      opSUB: Result := ValFromInt(L - R);
      opMUL: Result := ValFromInt(L * R);
      opIDIV: Result := ValFromInt(L div R);
      opMOD: Result := ValFromInt(L mod R);
      opSHL: Result := ValFromInt(L shl R);
      opSHR: Result := ValFromInt(L shr R);
      opAND: Result := ValFromInt(L and R);
      opOR: Result := ValFromInt(L or R);
      opXOR: Result := ValFromInt(L xor R);
      else
        ValOpErr;
    end;
  end;

  function I64Op(const Left, Right: TValueRec; Op: TExprOpCode): TValueRec;
  var
    L, R: int64;
  begin
    L := ValToInt(Left);
    R := ValToInt(Right);
    case Op of
      opADD: Result := ValFromInt(L + R);
      opSUB: Result := ValFromInt(L - R);
      opMUL: Result := ValFromInt(L * R);
      opIDIV: Result := ValFromInt(L div R);
      opMOD: Result := ValFromInt(L mod R);
      opSHL: Result := ValFromInt(L shl R);
      opSHR: Result := ValFromInt(L shr R);
      opAND: Result := ValFromInt(L and R);
      opOR: Result := ValFromInt(L or R);
      opXOR:
        Result := ValFromInt(L xor R);
      else
        ValOpErr;
    end;
  end;

  function FltOp(const Left, Right: TValueRec; Op: TExprOpCode): TValueRec;
  var
    L, R: real;
  begin
    L := ValToReal(Left);
    R := ValToReal(Right);
    case Op of
      opADD: Result := ValFromReal(L + R);
      opSUB: Result := ValFromReal(L - R);
      opMUL: Result := ValFromReal(L * R);
      opFDIV: Result := ValFromReal(L / R);
      else
        ValOpErr;
    end;
  end;

  function CurOp(const Left, Right: TValueRec; OpCode: TExprOpCode): TValueRec;
  var
    L, R: currency;
  begin
    L := ValToCurr(Left);
    R := ValToCurr(Right);
    case OpCode of
      opADD: Result := ValFromReal(L + R);
      opSUB: Result := ValFromReal(L - R);
      opMUL: Result := ValFromReal(L * R);
      opFDIV: Result := ValFromReal(L / R);
      else
        ValOpErr;
    end;
  end;

  function StrOp(const Left, Right: TValueRec; Op: TExprOpCode): TValueRec;
  begin
    if Op = opADD then
      Result := ValFromStr(ValToStr(Left) + ValToStr(Right))
    else
      ValOpErr;
  end;

  function BolOp(const Left, Right: TValueRec; OpCode: TExprOpCode): TValueRec;
  begin
    case OpCode of
      opAND: Result := ValFromBool(ValToBool(Left) and ValToBool(Right));
      opOR: Result := ValFromBool(ValToBool(Left) or ValToBool(Right));
      opXOR: Result := ValFromBool(ValToBool(Left) xor ValToBool(Right));
      else
        ValOpErr;
    end;
  end;

  function SetOp(const Left, Right: TValueRec; OpCode: TExprOpCode): TValueRec;
  var
    L, R: TSetValue;
  begin
    L := ValToSet(Left);
    R := ValToSet(Right);
    case OpCode of
      opADD: Result := ValFromSet(TSetValue.Add(L, R));
      opSUB: Result := ValFromSet(TSetValue.Sub(L, R));
      opMUL: Result := ValFromSet(TSetValue.Mul(L, R));
    end;
  end;

const
  OpMap: array[vtEmpty..vtWChr, vtEmpty..vtWChr] of
    TBaseType = ((btInt, btInt, btI64, btFlt, btCur, btSet, btBol, btStr, btStr, btStr, btStr),
    (btInt, btInt, btI64, btFlt, btCur, btErr, btErr, btErr, btErr, btErr, btErr), (btI64, btI64, btI64,
    btFlt, btCur, btErr, btErr, btErr, btErr, btErr, btErr), (btFlt, btFlt, btFlt, btFlt,
    btFlt, btErr, btErr, btErr, btErr, btErr, btErr), (btCur, btCur, btCur, btFlt, btCur, btErr, btErr, btErr,
    btErr, btErr, btErr), (btSet, btErr, btErr, btErr, btErr, btSet, btErr, btErr, btErr, btErr, btErr),
    (btBol, btErr, btErr, btErr, btErr, btErr, btBol, btErr, btErr, btErr, btErr),
    (btStr, btStr, btErr, btErr, btErr, btErr, btErr, btStr, btStr, btStr, btStr), (btStr, btErr, btErr, btErr,
    btErr, btErr, btErr, btStr, btStr, btStr, btStr), (btErr, btErr, btErr, btErr, btErr,
    btErr, btErr, btStr, btStr, btStr, btStr), (btErr, btErr, btErr, btErr, btErr, btErr, btErr, btStr, btStr,
    btStr, btStr));

  function SimpleOp(const L, R: TValueRec; OpCode: TExprOpCode): TValueRec;
  begin
    case OpMap[v1.VT, v2.VT] of
      btInt: if Op = opFDIV then
          Result := FltOp(L, R, OpCode)
        else
          Result := IntOp(L, R, OpCode);
      btI64: if Op = opFDIV then
          Result := FltOp(L, R, OpCode)
        else
          Result := I64Op(L, R, OpCode);
      btFlt: if Op = opIDIV then
          Result := IntOp(L, R, OpCode)
        else
          Result := FltOp(L, R, OpCode);
      btCur: Result := CurOp(L, R, OpCode);
      btStr: Result := StrOp(L, R, OpCode);
      btBol: Result := BolOp(L, R, OpCode);
      btSet: Result := SetOp(L, R, OpCode);
      else
        ValOpErr;
    end;
  end;

begin
  if (v1.VT <= vtWChr) and (v2.VT <= vtWChr) then
    Result := SimpleOp(v1, v2, Op)
  else
    ValOpErr;
end;

function ValCmp(const v1, v2: TValueRec; op: TExprOpCode): TValueRec;
type
  TCmpResult = (crLess, crEqual, crGreater);

  function IntCmp(L, R: integer): TCmpResult;
  begin
    if L > R then
      Result := crGreater
    else if L < R then
      Result := crLess
    else
      Result := crEqual;
  end;

  function I64Cmp(L, R: int64): TCmpResult;
  begin
    if L > R then
      Result := crGreater
    else if L < R then
      Result := crLess
    else
      Result := crEqual;
  end;

  function FltCmp(L, R: real): TCmpResult;
  begin
    if L > R then
      Result := crGreater
    else if L < R then
      Result := crLess
    else
      Result := crEqual;
  end;

  function CurCmp(L, R: currency): TCmpResult;
  begin
    if L > R then
      Result := crGreater
    else if L < R then
      Result := crLess
    else
      Result := crEqual;
  end;

  function StrCmp(const L, R: TValueRec): TCmpResult;
  var
    S1, S2: WideString;
  begin
    S1 := ValToWStr(L);
    S2 := ValToWStr(R);
    Result := IntCmp(WideCompareStr(S1, S2), 0);
  end;

  function SetCmp(L, R: TSetValue; OpCode: TExprOpCode): boolean;
  begin
    case OpCode of
      opLE: Result := R.Include(L);
      opGE: Result := L.Include(R);
      opEQ: Result := L.Equal(R);
      opNE: Result := not L.Equal(R);
      else
      begin
        ValOpErr;
        Result := False;
      end;
    end;
  end;

const
  OpMap: array[vtEmpty..vtWChr, vtEmpty..vtWChr] of TBaseType = ((
    btInt, btInt, btI64, btFlt, btCur, btSet, btBol, btStr, btStr, btStr, btStr),
    (btInt, btInt, btI64, btFlt, btCur, btErr, btErr, btErr, btErr, btErr, btErr), (btI64, btI64, btI64, btFlt, btCur,
    btErr, btErr, btErr, btErr, btErr, btErr), (btFlt, btFlt, btFlt, btFlt, btFlt, btErr,
    btErr, btErr, btErr, btErr, btErr), (btCur, btCur, btCur, btFlt, btCur, btErr, btErr, btErr, btErr, btErr,
    btErr), (btSet, btErr, btErr, btErr, btErr, btSet, btErr, btErr, btErr, btErr, btErr),
    (btBol, btErr, btErr, btErr, btErr, btErr, btBol, btErr, btErr, btErr, btErr), (btStr, btErr, btErr,
    btErr, btErr, btErr, btErr, btStr, btStr, btStr, btStr), (btStr, btErr, btErr, btErr,
    btErr, btErr, btErr, btStr, btStr, btStr, btStr), (btStr, btErr, btErr, btErr, btErr, btErr, btErr, btStr,
    btStr, btStr, btStr), (btStr, btErr, btErr, btErr, btErr, btErr, btErr, btStr, btStr, btStr, btStr));
var
  CmpRet: TCmpResult;
  Ret: boolean;
begin
  if (v1.VT <= vtWChr) and (v2.VT <= vtWChr) then
  begin
    case OpMap[v1.VT, v2.VT] of
      btInt: CmpRet := IntCmp(ValToInt(v1), ValToInt(v2));
      btI64: CmpRet := I64Cmp(ValToInt64(v1), ValToInt64(v2));
      btFlt: CmpRet := FltCmp(ValToReal(v1), ValToReal(v2));
      btCur: CmpRet := CurCmp(ValToCurr(v1), ValToCurr(v2));
      btBol: CmpRet := IntCmp(integer(ValToBool(v1)), integer(ValToBool(v2)));
      btStr: CmpRet := StrCmp(v1, v2);
      btSet:
      begin
        Result := ValFromBool(SetCmp(ValToSet(v1), ValToSet(v2), op));
        Exit;
      end;
      else
      begin
        ValOpErr;
        CmpRet := crLess;
      end;
    end;
    case op of
      opNE: Ret := CmpRet <> crEqual;
      opEQ: Ret := CmpRet = crEqual;
      opLT: Ret := CmpRet = crLess;
      opLE: Ret := CmpRet <= crEqual;
      opGT: Ret := CmpRet = crGreater;
      opGE: Ret := CmpRet >= crEqual;
      else
      begin
        ValOpErr;
        Ret := False;
      end;
    end;
    Result := ValFromBool(Ret);
  end
  else
    ValOpErr;
end;

function ValIn(const v1, v2: TValueRec): TValueRec;
begin
  Result := ValFromBool(ValToSet(v2).TestBits(ValToInt(v1)));
end;

function ValNot(const v1: TValueRec): TValueRec;
begin
  case v1.VT of
    vtInt: Result := ValFromInt(not v1.VInt);
    vtInt64: Result := ValFromInt(not v1.VInt64);
    vtBool: Result := ValFromBool(not v1.VBool <> 0);
    else
      ValOpErr;
  end;
end;

function ValNeg(const v1: TValueRec): TValueRec;
begin
  case
    v1.VT of
    vtInt: Result := ValFromInt(-v1.VInt);
    vtInt64: Result := ValFromInt(-v1.VInt64);
    vtReal: Result := ValFromReal(-v1.VReal);
    vtCurr: Result := ValFromCurr(-v1.VCurr);
    else
      ValOpErr;
  end;
end;

function ValAbs(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromInt(Abs(V.VInt));
    vtInt64: Result := ValFromInt(Abs(V.VInt64));
    vtReal: Result := ValFromReal(Abs(V.VReal));
    vtCurr: Result := ValFromCurr(Abs(V.VCurr));
    else
      ValFuncErr;
  end;
end;

function ValHi(const V: TValueRec; typ: TIntType): TValueRec;
var
  I: int64;
begin
  I := ValToInt64(V);
  case typ.Kind of
    intS16, intU16: Result := ValFromInt((word(I) shr 8) and $00FF);
    intS32, intU32: Result := ValFromInt((longword(I) shr 16) and $0000FFFF);
    intS64, intU64: Result := ValFromInt((I shr 32) and $00000000FFFFFFFF);
    else
      Result := ValFromInt(0);
  end;
end;

function ValLo(const V: TValueRec; typ: TIntType): TValueRec;
var
  I: int64;
begin
  I := ValToInt64(V);
  case typ.Kind of
    intS32, intU32: Result := ValFromInt(longword(I) and $0000FFFF);
    intS64, intU64: Result := ValFromInt(I and $00000000FFFFFFFF);
    else
      Result := ValFromInt(word(I) and $00FF);
  end;
end;

function ValChr(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromChar(Chr(V.VInt));
    vtInt64: Result := ValFromChar(Chr(V.VInt64));
    else
      ValFuncErr;
  end;
end;

function ValOdd(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromBool(Odd(V.VInt));
    vtInt64: Result := ValFromBool(Odd(V.VInt64));
    else
      ValFuncErr;
  end;
end;

function ValOrd(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromInt(V.VInt);
    vtInt64: Result := ValFromInt(V.VInt64);
    vtBool: Result := ValFromInt(Ord(V.VBool));
    vtAChr: Result := ValFromInt(Ord(V.VAChr));
    vtWChr: Result := ValFromInt(word(V.VWChr));
    else
      ValFuncErr;
  end;
end;

function ValPred(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromInt(Pred(V.VInt));
    vtInt64: Result := ValFromInt(Pred(V.VInt64));
    vtAChr: Result := ValFromChar(Pred(V.VAChr));
    vtWChr: Result := ValFromWChar(widechar(V.VWChr - 1));
    else
      ValFuncErr;
  end;
end;

function ValRound(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromInt(V.VInt);
    vtInt64: Result := ValFromInt(V.VInt64);
    vtReal: Result := ValFromInt(Round(V.VReal));
    vtCurr: Result := ValFromInt(Round(V.VCurr));
    else
      ValFuncErr;
  end;
end;

function ValSucc(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromInt(Succ(V.VInt));
    vtInt64: Result := ValFromInt(Succ(V.VInt64));
    vtAChr: Result := ValFromChar(Succ(V.VAChr));
    vtWChr: Result := ValFromWChar(widechar(V.VWChr + 1));
    else
      ValFuncErr;
  end;
end;

function ValSwap(const V: TValueRec; typ: TIntType): TValueRec;

  function DoSwap16(w: word): word;
  begin
    Result := ((w shr 8) and $00ff) or (w shl 8);
  end;

  function DoSwap32(w: longword): longword;
  begin
    Result := ((w shr 16) and $0000ffff) or (w shl 16);
  end;

  function DoSwap64(w: int64): int64;
  begin
    Result := ((w shr 32) and $00000000ffffffff) or (w shl 32);
  end;

var
  I: int64;
begin
  I := ValToInt64(V);
  case typ.Kind of
    intS32, intU32: Result := ValFromInt(DoSwap32(longword(I)));
    intS64, intU64: Result := ValFromInt(DoSwap64(I));
    else
      Result := ValFromInt(DoSwap16(word(I)));
  end;
end;

function ValTrunc(const V: TValueRec): TValueRec;
begin
  case V.VT of
    vtInt: Result := ValFromInt(V.VInt);
    vtInt64: Result := ValFromInt(V.VInt64);
    vtReal: Result := ValFromInt(Trunc(V.VReal));
    vtCurr: Result := ValFromInt(Trunc(V.VCurr));
    else
      ValFuncErr;
  end;
end;

function ValIsCompatible(const V: TValueRec; typ: TType): boolean;
begin
  case typ.TypeCode of
    typBool: Result := V.VT = vtBool;
    typChar: if TCharType(typ).Kind = charAnsi then
        Result := V.VT = vtAChr
      else
        Result := V.VT = vtWChr;
    typInt, typEnum, typSubrange: Result := V.VT in [vtInt, vtInt64];
    typNumeric: Result := V.VT in [vtReal, vtCurr, vtInt, vtInt64];
    typString: Result := V.VT in [vtStr, vtWStr];
    typPointer: if typ.IsPAnsiChar or typ.IsPWideChar then
        Result := V.VT in [vtStr, vtWStr]
      else
        Result := V.VT in [vtAddrOfSymbol, vtSymbol, vtPtr];
    typPAnsiChar, typPWideChar: Result := V.VT in [vtStr, vtWStr];
    typRecord: Result := V.VT = vtRecord;
    typSet: Result := V.VT = vtSet;
    typArray: Result := V.VT = vtArray;
    typClass, typInterface, typDynamicArray: Result := V.VT in [vtAddrOfSymbol, vtSymbol, vtPtr];
    typClassRef, typProcedural: Result := V.VT in [vtSymbol, vtPtr];
    else
      Result := False;
  end;
end;

var
  _Directives: TStringList;

procedure InitDirectives;
const
  Idents: array[TDirectiveIdent] of string =
    ('', 'deprecated', 'library', 'platform', 'experimental', 'unimplemented', 'register', 'pascal',
    'cdecl', 'stdcall', 'safecall', 'virtual', 'dynamic', 'abstract', 'override', 'overload',
    'message', 'reintroduce', 'static', 'inline', 'assembler', 'varargs', 'local', 'dispid',
    'export', 'near', 'far', 'external', 'forward');
var
  I: TDirectiveIdent;
begin
  _Directives := TStringList.Create;
  _Directives.Sorted := True;
  for I := idDeprecated to idForward do
    _Directives.AddObject(Idents[I], TObject(integer(I)));
end;

function FindDirective(const S: TSymString): TDirectiveIdent;
var
  I: integer;
begin
  if _Directives.Find(S, I) then
    Result := TDirectiveIdent(_Directives.Objects[I])
  else
    Result := idNone;
end;

function TypIsVariantCompatible(typ: TType): boolean;
begin
  Result := typ.TypeCode in [typInt, typNumeric, typBool, typChar, typString, typVariant,
    typEnum, typSubrange, typInterface];
end;

function TypIsVariantArithCompatible(typ: TType): boolean;
begin
  Result := typ.TypeCode in [typInt, typNumeric, typBool, typChar, typPAnsiChar, typPWideChar,
    typString, typVariant, typEnum, typSubrange, typInterface];
  if not Result then
    Result := typ.IsPackedString;
end;

function TypIsStringArithCompatible(typ: TType): boolean;
begin
  Result := typ.TypeCode in [typString, typChar, typPAnsiChar, typPWideChar, typVariant];
  if not Result then
    Result := typ.IsPackedString;
end;

constructor TAstNode.Create;
begin
end;

destructor TAstNode.Destroy;
begin
  inherited;
end;

procedure TSymbol.Add(Sym: TSymbol);
begin
  raise EASTError.CreateFmt('Add not implemented in %s', [Self.ClassName]);
end;

procedure TSymbol.AddSymbol(Sym: TSymbol);
begin
  raise EASTError.CreateFmt('AddSymbol not implemented in %s', [Self.ClassName]);
end;

function TSymbol.GetFullName: TSymString;
var
  Sym: TSymbol;
begin
  Result := '';
  Sym := Self;
  while Sym <> nil do
  begin
    if Sym <> Self then
      Result := '.' + Result;
    Result := Sym.Name + Result;
    Sym := Sym.Parent;
  end;
end;

function TSymbol.GetModule: TModule;
var
  Sym: TSymbol;
begin
  Sym := Self;
  while Assigned(Sym) and (Sym.NodeKind <> nkModule) do
    Sym := Sym.Parent;
  if not Assigned(Sym) or (Sym.NodeKind <> nkModule) then
    raise EASTError.CreateFmt('Symbol %s has not module', [Self.Name]);
  Result := TModule(Sym);
end;

function TSymbol.GetSymName: TSymString;
var
  Sym: TSymbol;
begin
  Result := '';
  Sym := Self;
  while Sym <> nil do
  begin
    if Sym <> Self then
      Result := '.' + Result;
    Result := Sym.Name + Result;
    Sym :=
      Sym.Parent;
    if Sym.NodeKind = nkModule then
      Break;
  end;
end;

function TSymbol.GetUnitName: string;
var
  M: TModule;
begin
  M := GetModule;
  if Assigned(M) then
    Result := M.Name
  else
    Result := '';
end;

procedure TModule.Add(Sym: TSymbol);
begin
  Symbols.Add(Sym);
end;

procedure TModule.AddPrivate(Node: TAstNode);
begin
  FPrivateNodes.Add(Node);
end;

procedure TModule.AddSymbol(Sym: TSymbol);
begin
  if Sym.Parent <> nil then
    raise EASTError.CreateFmt(SErr_SymbolHasParent, [Sym.Name]);
  Sym.Parent := Self;
end;

constructor TModule.Create;
begin
  inherited;
  FNodeKind := nkModule;
  Symbols := TSymbolTable.Create(Self);
  Symbols.Capacity := 64;
  InternalSymbols := TSymbolTable.Create(Self);
  InternalSymbols.Capacity := 64;
  LoadedUnits := TSymbolTable.Create(nil);
  LoadedUnits.AutoAddToOwner := False;
  PointerSize := SizeOf(Pointer);
  FPrivateNodes := TFPList.Create;
  FPrivateNodes.Capacity := 1024;
end;

destructor TModule.Destroy;

  procedure FreeNodes;
  var
    i: integer;
  begin
    for i := 0 to FPrivateNodes.Count - 1 do
      TObject(FPrivateNodes[i]).Free;
    FPrivateNodes.Free;
  end;

begin
  Symbols.Free;
  InternalSymbols.Free;
  LoadedUnits.Free;
  FType.Free;
  FreeNodes;
  inherited;
end;

function TModule.FindSymbol(const S: TSymString): TSymbol;
begin
  Result := Symbols.Find(S);
end;

function TModule.GetType: TType;
begin
  if FType = nil then
  begin
    FType := TSymbolType.Create;
    FType.Parent := Self.Parent;
    TSymbolType(FType).Reference := Self;
  end;
  Result := FType;
end;

procedure TModule.SetNameScope(const Scopes: array of TSymString; Count: integer);
var
  I: integer;
begin
  SetLength(Names, Count);
  Self.Name := '';
  for I := 0 to High(Names) do
  begin
    Names[I] := Scopes[I];
    if I > 0 then
      Self.Name := Self.Name + '.';
    Self.Name := Self.Name + Names[I];
  end;
end;

procedure TNameScope.Add(const S: TSymString; Sym: TSymbol);
var
  I: integer;
begin
  if not FSubNames.Find(S, I) then
    FSubNames.AddObject(S, Sym);
end;

constructor TNameScope.Create;
begin
  inherited;
  FSubNames := TStringList.Create;
  FSubNames.Sorted := True;
end;

destructor TNameScope.Destroy;
begin
  FSubNames.Free;
  FType.Free;
  inherited;
end;

function TNameScope.FindSymbol(const S: TSymString): TSymbol;
var
  I: integer;
begin
  if FSubNames.Find(S, I) then
    Result := TSymbol(FSubNames.Objects[I])
  else
    Result := nil;
end;

function TNameScope.GetType: TType;
begin
  if FType = nil then
  begin
    FType := TSymbolType.Create;
    FType.Parent := Self.Parent;
    TSymbolType(FType).Reference := Self;
  end;
  Result := FType;
end;

function TType.BaseCode: TBaseTypeCode;
const
  IntBtcMaps: array[TIntKind] of TBaseTypeCode =
    (btcShortint, btcByte, btcSmallint, btcWord, btcLongint, btcLongWord, btcInt64, btcUInt64);
  NumBtcMaps: array[TNumericKind] of TBaseTypeCode =
    (btcSingle, btcDouble, btcExtended, btcCurrency, btcComp, btcReal48);
  CharBtcMaps: array
    [TCharKind] of TBaseTypeCode = (btcAnsiChar, btcWideChar);
  BoolBtcMaps: array[TBoolKind] of TBaseTypeCode = (btcBoolean, btcByteBool, btcWordBool, btcLongBool);
  StrBtcMaps: array
    [TStringKind] of TBaseTypeCode = (btcAnsiString, btcWideString, btcUnicodeString, btcShortString, btcWShortString);
  VarBtcMaps: array[boolean] of TBaseTypeCode = (btcVariant, btcOleVariant);
  IntfBtcMaps: array[boolean] of TBaseTypeCode = (btcInterface, btcDispInterface);
  BtcMaps: array[TTypeCode] of TBaseTypeCode =
    (btcUnknown, btcUntype, btcLongint, btcDouble, btcBoolean, btcAnsiChar, btcPointer, btcPAnsiChar,
    btcPWideChar, btcAnsiString, btcVariant, btcFile, btcText, btcProcedural, btcRecord, btcObject,
    btcClass, btcInterface, btcClassRef, btcEnum, btcSet, btcSubrange, btcArray, btcDynamicArray,
    btcUnknown, btcUnknown, btcUnknown, btcOpenArray, btcUnknown);
begin
  case TypeCode of
    typInt: Result := IntBtcMaps[TIntType(Self).Kind];
    typNumeric: Result := NumBtcMaps[TNumericType(Self).Kind];
    typBool: Result := BoolBtcMaps[TBoolType(Self).Kind];
    typChar: Result := CharBtcMaps[TCharType(Self).Kind];
    typString: Result := StrBtcMaps[TStringType(Self).Kind];
    typVariant: Result := VarBtcMaps[TVariantType(Self).IsOle];
    typInterface: Result := IntfBtcMaps[TInterfaceType(Self).IsDisp];
    typAlias, typClonedType: Result := TAliasType(Self).RefType.BaseCode;
    else
      Result := BtcMaps[Self.TypeCode];
  end;
end;

constructor TType.Create;
begin
  inherited Create;
  FNodeKind := nkType;
end;

procedure TType.CreatePointerType(ASize: cardinal);
begin
  if FPointerType = nil then
  begin
    FPointerType := TPointerType.Create;
    FPointerType.Parent := Self.Parent;
    FPointerType.Size := SizeOf(Pointer);
    TPointerType(FPointerType).RefType := Self;
  end;
end;

destructor TType.Destroy;
begin
  FPointerType.Free;
  inherited;
end;

function TType.Equals(typ: TType): Boolean;

  function ParamEquals(A1, A2: TFuncParam): boolean;
  begin
    Result := (A1.ArgKind = A2.ArgKind) and (A1.Modifier = A2.Modifier) and (A1.ParamType.Equals(A2.ParamType));
  end;

  function RetEquals(T1, T2: TType): boolean;
  begin
    if (T1 = nil) or (T2 = nil) then
      Result := T2 = T1
    else
      Result := T1.Equals(T2);
  end;

  function ProcEquals(P1, P2: TProceduralType): boolean;

    function AllParamsEqual(P1, P2: TProceduralType): boolean;
    var
      i: integer;
    begin
      for i := 0 to P1.ParamCount - 1 do
        if not ParamEquals(P1.Params[i], P2.Params[i]) then
        begin
          Result := False;
          Exit;
        end;
      Result := True;
    end;

  begin
    Result := (P1.IsMethodPointer = P2.IsMethodPointer) and (P1.ParamCount = P2.ParamCount) and
      (P1.CallConvention = P2.CallConvention) and RetEquals(P1.ReturnType, P2.ReturnType) and AllParamsEqual(P1, P2);
  end;

  function SameSet(s1, s2: TSetType): boolean;
  var
    r1, r2: TSubrangeType;
  begin
    r1 := s1.RangeType;
    r2 := s2.RangeType;
    Result := ((r1 = nil) and (r2 = nil)) or ((r1.BaseType.Equals(r2.BaseType)) and
      (s1.LowByte = s2.LowByte) and (s1.HighByte = s2.HighByte));
  end;

  function SamePtr(p1, p2: TPointerType): boolean;
  begin
    Result := (p1.RefType = p2.RefType) or ((p1.RefType <> nil) and (p2.RefType <> nil) and
      (p1.RefType.Equals(p2.RefType)));
  end;

var
  src: TType;
begin
  src := Self.OriginalType;
  typ := typ.OriginalType;
  Result := src.TypeCode = typ.TypeCode;
  if Result then
    case typ.TypeCode of
      typInt: Result := TIntType(src).Kind = TIntType(typ).Kind;
      typChar: Result := TCharType(src).Kind = TCharType(typ).Kind;
      typBool: Result := TBoolType(src).Kind = TBoolType(typ).Kind;
      typNumeric: Result := TNumericType(src).Kind = TNumericType(typ).Kind;
      typString: Result := (TStringType(src).Kind = TStringType(typ).Kind) and
          (TStringType(src).CodePage = TStringType(typ).CodePage) and
          (TStringType(src).CharCount = TStringType(typ).CharCount);
      typPointer: Result := SamePtr(TPointerType(Self), TPointerType(typ));
      typProcedural: Result := ProcEquals(TProceduralType(Self), TProceduralType(typ));
      typRecord, typObject, typClass, typInterface: Result := (src = typ);
      typClassRef: Result := (TClassRefType(src).RefType = TClassRefType(typ).RefType);
      typEnum, typArray, typDynamicArray, typFile: Result := (src = typ);
      typSet: Result := SameSet(TSetType(src), TSetType(typ));
      typSubrange: Result := TSubrangeType(src).BaseType.Equals(TSubrangeType(typ).BaseType);
      typOpenArray: Result := TOpenArrayType(src).ElementType.Equals(TOpenArrayType(typ).ElementType);
    end;
end;

function TType.GetAlignSize: byte;
begin
  Result := FSize;
end;

function TType.IsAnsiShortString: boolean;
begin
  Result := (TypeCode = typString) and (TStringType(Self).Kind = strAShort);
end;

function TType.IsAnsiString: boolean;
begin
  Result := (TypeCode = typString) and (TStringType(Self).Kind = strAnsi);
end;

function TType.IsBoolean: boolean;
begin
  if TypeCode = typBool then
    Result := True
  else
    Result := (TypeCode = typSubrange) and (TSubrangeType(Self).BaseType.TypeCode = typBool);
end;

function TType.IsComp: boolean;
begin
  Result := (TypeCode = typNumeric) and (TNumericType(Self).Kind = numComp);
end;

function TType.IsCurrency: boolean;
begin
  Result := (TypeCode = typNumeric) and (TNumericType(Self).Kind = numCurrency);
end;

function TType.IsSingle: boolean;
begin
  Result := (TypeCode = typNumeric) and (TNumericType(Self).Kind = numSingle);
end;

function TType.IsInteger: boolean;
begin
  if TypeCode = typInt then
    Result := True
  else
    Result := (TypeCode = typSubrange) and (TSubrangeType(Self).BaseType.TypeCode = typInt);
end;

function TType.IsInt32: boolean;
begin
  if TypeCode = typInt then
    Result := TIntType(Self).Kind = intS32
  else
    Result := (TypeCode = typSubrange) and (TSubrangeType(Self).BaseType.IsInt32);
end;

function TType.IsMethodPointer: boolean;
begin
  Result := (TypeCode = typProcedural) and TProceduralType(Self).IsMethodPointer;
end;

function TType.IsOrdinal: boolean;
begin
  Result := TypeCode in [typInt, typChar, typBool, typSubrange, typEnum];
end;

function TType.IsPackedString: boolean;
begin
  Result := (TypeCode = typArray) and (TArrayType(Self).DimensionCount = 1) and
    (TArrayType(Self).ElementType.TypeCode = typChar);
end;

function TType.IsPackedStringAnsi: boolean;
begin
  Result := (TypeCode = typArray) and (TArrayType(Self).DimensionCount = 1) and
    (TArrayType(Self).ElementType.TypeCode = typChar) and (TCharType(TArrayType(Self).ElementType).Kind = charAnsi);
end;

function TType.IsPackedStringWide: boolean;
begin
  Result := (TypeCode = typArray) and (TArrayType(Self).DimensionCount = 1) and
    (TArrayType(Self).ElementType.TypeCode = typChar) and (TCharType(TArrayType(Self).ElementType).Kind = charWide);
end;

function TType.IsPAnsiChar: boolean;
begin
  Result := (TypeCode = typPAnsiChar) or ((TypeCode = typPointer) and
    (TPointerType(Self).RefType.TypeCode = typChar) and (TCharType(TPointerType(Self).RefType).Kind = charAnsi));
end;

function TType.IsPointer: boolean;
begin
  Result := TypeCode in [typPointer, typPAnsiChar, typPWideChar];
end;

function TType.IsPointerBased: boolean;
begin
  Result := TypeCode in [typPointer, typPAnsiChar, typPWideChar, typClass, typClassRef, typInterface, typDynamicArray];
  if not Result then
    Result := ((TypeCode = typString) and (TStringType(Self).Kind in [strAnsi, strWide, strUnicode])) or
      ((TypeCode = typProcedural) and not TProceduralType(Self).IsMethodPointer);
end;

function TType.IsProcedural: boolean;
begin
  Result := TypeCode = typProcedural;
end;

function TType.IsPWideChar: boolean;
begin
  Result := (TypeCode = typPWideChar) or ((TypeCode = typPointer) and
    (TPointerType(Self).RefType.TypeCode = typChar) and (TCharType(TPointerType(Self).RefType).Kind = charWide));
end;

function TType.IsReal: boolean;
begin
  Result := TypeCode = typNumeric;
end;

function TType.IsShortString: boolean;
begin
  Result := (TypeCode = typString) and (TStringType(Self).Kind in [strAShort, strWShort]);
end;

function TType.IsSigned: boolean;
begin
  if TypeCode = typInt then
    Result := TIntType(Self).Kind in [intS8, intS16, intS32, intS64]
  else if TypeCode = typNumeric then
    Result := True
  else
    Result := (TypeCode = typSubrange) and TSubrangeType(Self).BaseType.IsSigned;
end;

function TType.IsSignedInt: boolean;
begin
  if TypeCode = typInt then
    Result := TIntType(Self).Kind in [intS8, intS16, intS32, intS64]
  else
    Result := (TypeCode = typSubrange) and TSubrangeType(Self).BaseType.IsSignedInt;
end;

function TType.IsStdBool: boolean;
begin
  if TypeCode = typBool then
    Result := TBoolType(Self).Kind = bolStd
  else
    Result := (TypeCode = typSubrange) and (TSubrangeType(Self).BaseType.IsStdBool);
end;

function TType.IsStringArithCompatible: boolean;
begin
  Result := TypeCode in [typString, typChar, typPAnsiChar, typPWideChar, typVariant];
  if not Result then
    Result := IsPackedString;
end;

function TType.IsStringCompatible: boolean;
begin
  Result := (TypeCode = typString) or IsPackedString;
end;

function TType.IsUnicodeString: boolean;
begin
  Result := (TypeCode = typString) and (TStringType(Self).Kind = strUnicode);
end;

function TType.IsUntypePointer: boolean;
begin
  Result := (TypeCode = typPointer) and (TPointerType(Self).RefType = nil);
end;

function TType.IsVariantCompatible: boolean;
begin
  Result := TypeCode in [typInt, typNumeric, typBool, typChar, typString, typVariant, typEnum,
    typSubrange, typInterface];
end;

function TType.IsWideShortString: boolean;
begin
  Result := (TypeCode = typString) and (TStringType(Self).Kind = strWShort);
end;

function TType.IsWideString: boolean;
begin
  Result := (TypeCode = typString) and (TStringType(Self).Kind = strWide);
end;

function TType.NormalType: TType;
begin
  Result := OriginalType;
  if Result.TypeCode = typSubrange then
    Result := TSubrangeType(Result).BaseType;
end;

function TType.OriginalType: TType;
begin
  Result := Self;
  while True do
  begin
    if Result = nil then Break;
    if Result.TypeCode = typAlias then
      Result := TAliasType(Result).RefType
    else if Result.TypeCode = typClonedType then
      Result := TClonedAliasType(Result).RefType
    else
      Break;
  end;
end;

constructor TPrimitiveType.Create(ACode: TTypeCode);
begin
  inherited Create;
  FTypeCode := ACode;
end;

function TPrimitiveType.GetAlignSize: byte;
begin
  if FAlign > 0 then
    Result := FAlign
  else
    Result := inherited GetAlignSize;
end;

constructor TUnresolvedType.Create;
begin
  inherited;
  FTypeCode := typUntype;
end;

constructor TAliasType.Create;
begin
  inherited;
  FTypeCode := typAlias;
end;

procedure TAliasType.Update;
begin
  FSize := RefType.FSize;
end;

constructor TClonedAliasType.Create;
begin
  inherited;
  FTypeCode := typClonedType;
end;

function TIntType.GetAlignSize: byte;
begin
  Result := Size;
end;

constructor TIntType.Create;
begin
  inherited Create;
  FTypeCode := typInt;
end;

constructor TBoolType.Create;
begin
  inherited Create;
  FTypeCode := typBool;
end;

constructor TCharType.Create;
begin
  inherited Create;
  FTypeCode := typChar;
end;

constructor TNumericType.Create;
begin
  inherited Create;
  FTypeCode := typNumeric;
end;

constructor TStringType.Create(AKind: TStringKind);
begin
  inherited Create;
  FTypeCode := typString;
  FKind := AKind;
  case FKind of
    strAnsi, strWide, strUnicode: FSize := SizeOf(Pointer);
    else
      Assert(FKind in [strAShort, strWShort], 'TStringType.Create: Invalid TStringKind');
      FCharCount := 255;
      Update;
  end;
end;

function TStringType.GetAlignSize: byte;
begin
  case FKind of
    strAShort: Result :=
        1;
    strWShort: Result := 2
    else
      Result := FSize;
  end;
end;

procedure TStringType.Update;
begin
  case FKind of
    strAShort: FSize := CharCount + 2;
    strWShort: FSize := (CharCount + 2) * 2;
  end;
end;

constructor TVariantType.Create;
begin
  inherited;
  FTypeCode := typVariant;
end;

function TVariantType.GetAlignSize: byte;
begin
  {$ifdef CPU386}
  Result := 8;
  {$endif}
  {$ifdef CPU64}
  Result := 16;
  {$endif}
end;

constructor TPointerType.Create;
begin
  inherited;
  FTypeCode := typPointer;
end;

function TPointerType.IsUntype: boolean;
begin
  Result := (RefType = nil) or (RefType.TypeCode = typUntype);
end;

constructor TArrayType.Create;
begin
  inherited;
  FTypeCode := typArray;
end;

function TArrayType.GetAlignSize: byte;
begin
  if IsPacked then
    Result := 1
  else
    Result := ElementType.AlignSize;
end;

function TArrayType.GetDimensionCount: integer;
var
  Arr: TArrayType;
begin
  Result := 1;
  Arr := Self;
  while Arr.ElementType.TypeCode = typArray do
  begin
    Arr := TArrayType(Arr.ElementType);
    Inc(Result);
  end;
end;

function TArrayType.GetElementCount: int64;
begin
  Result := Range.RangeEnd - Range.RangeBegin + 1;
end;

procedure TArrayType.Update;
var
  T: TType;
begin
  if not Assigned(ElementType) then
    FSize := 0
  else
  begin
    FSize := cardinal(Range.RangeEnd - Range.RangeBegin + 1) * ElementType.Size;
    ArrayAttr := [];
    T := ElementType;
    case T.TypeCode of
      typRecord:
      begin
        if staNeedInit in TRecordType(T).RecordAttr then
          Include(ArrayAttr, staNeedInit);
        if staNeedFree in TRecordType(T).RecordAttr then
          Include(ArrayAttr, staNeedFree);
      end;
      typArray:
      begin
        if staNeedInit in TArrayType(T).ArrayAttr then
          Include(ArrayAttr, staNeedInit);
        if staNeedFree in TArrayType(T).ArrayAttr then
          Include(ArrayAttr, staNeedFree);
      end;
      else
        if T.TypeCode in AutoInitTypes then
          Include(ArrayAttr, staNeedInit);
        if T.TypeCode in AutoFreeTypes then
          Include(ArrayAttr, staNeedFree);
    end;
  end;
end;

constructor TDynamicArrayType.Create;
begin
  inherited;
  FTypeCode := typDynamicArray;
end;

function TDynamicArrayType.GetAlignSize: byte;
begin
  if IsPacked then
    Result := 1
  else
    Result := ElementType.AlignSize;
end;

constructor TOpenArrayType.Create;
begin
  inherited;
  FTypeCode := typOpenArray;
end;

function TOpenArrayType.GetAlignSize: byte;
begin
  Assert(ElementType <> nil, 'TOpenArrayType.GetAlignSize');
  Result := ElementType.AlignSize;
end;

procedure TEnumType.CalcSize(MinSize: integer);
var
  hiSize, loSize: integer;
begin
  if MinSize = 4 then
  begin
    FSize := 4;
    Exit;
  end;
  if FLowValue < 0 then
  begin
    if FHighValue > 32767 then
      hiSize := 4
    else if FHighValue > 127 then
      hiSize := 2
    else
      hiSize := 1;
    if FLowValue < -32768 then
      loSize := 4
    else if FLowValue < -128 then
      loSize := 2
    else
      loSize := 1;
  end
  else
  begin
    if FHighValue > 65535 then
      hiSize := 4
    else if FHighValue > 255 then
      hiSize := 2
    else
      hiSize := 1;
    if FLowValue < -32768 then
      loSize := 4
    else if FLowValue < -128 then
      loSize :=
        2
    else
      loSize := 1;
  end;
  if hiSize > loSize then
    FSize := hiSize
  else
    FSize := loSize;
  if integer(FSize) < MinSize then
    FSize := MinSize;
end;

constructor TEnumType.Create;
begin
  inherited
  Create;
  FTypeCode := typEnum;
  Values := TFPList.Create;
  Values.Capacity := 32;
  MinEnumSize := 1;
end;

destructor TEnumType.Destroy;
begin
  Values.Free;
  inherited;
end;

procedure TEnumType.Update;
begin
  UpdateRange;
  CalcSize(MinEnumSize);
end;

procedure TEnumType.UpdateRange;
var
  I: integer;
begin
  if Values.Count < 1 then
    raise EASTError.Create('empty enum');
  FHighValue := TEnumValue(Values[0]).Value;
  FLowValue := TEnumValue(Values[0]).Value;
  for
    I := 1 to Values.Count - 1 do
  begin
    with TEnumValue(Values[I]) do
    begin
      if FHighValue < Value then
        FHighValue := Value;
      if FLowValue > Value then
        FLowValue := Value;
    end;
  end;
end;

function TField.AlignOfParent: byte;
var
  P: TSymbol;
begin
  Result := 0;
  P := Parent;
  if (P <> nil) and (P.NodeKind = nkType) then
  begin
    case TType(P).TypeCode of
      typClass: Result := TClassType(P).GlobalAlignSize;
      typRecord: Result := TRecordType(P).GlobalAlignSize;
      typObject: Result := TObjectType(P).GlobalAlignSize;
    end;
  end;
end;

constructor TField.Create;
begin
  inherited;
  FNodeKind := nkField;
end;

procedure TMultiAccessor.Add(Field: TSymbol);
begin
  if Length(Fields) <= FieldCount then
    SetLength(Fields, FieldCount + 4);
  Fields[FieldCount] := Field;
  Inc(FieldCount);
end;

constructor TMultiAccessor.Create;
begin
  inherited;
  FNodeKind :=
    nkAccessor;
end;

function TMultiAccessor.First: TSymbol;
begin
  if FieldCount > 0 then
    Result := Fields[0]
  else
    Result := nil;
end;

function TMultiAccessor.Last: TField;
begin
  if FieldCount > 0 then
  begin
    if Fields[FieldCount - 1].NodeKind <> nkField then
      raise EASTError.Create('Invalid accessor');
    Result := TField(Fields[FieldCount - 1]);
  end
  else
    Result := nil;
end;

constructor TProperty.Create;
begin
  inherited;
  FNodeKind := nkProperty;
  Index := -2147483647 - 1;
end;

procedure TProperty.CreateParams;
begin
  if Params = nil then
    Params := TFuncParamList.Create;
end;

destructor TProperty.Destroy;
begin
  ValClear(DefaultValue);
  Params.Free;
  inherited;
end;

function TProperty.GetterType: TType;
begin
  if Getter = nil then
    Result := nil
  else
    case Getter.NodeKind of
      nkField: Result := TField(Getter).FieldType;
      nkMethod: Result := TMethod(Getter).ReturnType;
      nkAccessor: Result := TMultiAccessor(Getter).Last.FieldType;
      else
        raise EASTError.Create('Invalid getter');
    end;
end;

function TProperty.HasIndexSpec: boolean;
begin
  Result := Index <> -2147483647 - 1;
end;

function TProperty.ParamCount: integer;
begin
  if Params = nil then
    Result := 0
  else
    Result := Params.Count;
end;

function TProperty.SetterType: TType;
begin
  if Setter = nil then
    Result := nil
  else
    case Setter.NodeKind of
      nkField: Result := TField(Setter).FieldType;
      nkMethod: Result := TMethod(Setter).ReturnType;
      nkAccessor: Result := TMultiAccessor(Setter).Last.FieldType;
      else
        raise
        EASTError.Create('Invalid getter');
    end;
end;

procedure TRecordBody.AddFields(Symbols: TSymbolTable);
var
  I: integer;
  VarPart: TRecordVariant;
begin
  for I := 0 to Members.Count - 1 do
  begin
    Symbols.Add(TSymbol(Members[I]));
  end;
  if (Selector <> nil) and (Selector.Name <> '') then
  begin
    Symbols.Add(Selector);
  end;
  VarPart := Variants;
  while VarPart <> nil do
  begin
    VarPart.AddFields(Symbols);
    VarPart := VarPart.Next;
  end;
end;

constructor TRecordBody.Create;
begin
  Members := TFPList.Create;
  {$ifdef CPU386}
  MaxAlignSize := 4;
  {$endif}
  {$ifdef CPU64}
  MaxAlignSize := 8;
  {$endif}
end;

destructor TRecordBody.Destroy;
begin
  Members.Free;
  Variants.Free;
  inherited;
end;

function TRecordBody.RecordSize: int64;
var
  VarPart: TRecordVariant;
  I, Off, Size: cardinal;
begin
  if Variants <> nil then
  begin
    VarPart := Variants;
    Off := VarPart.Offset;
    Size := 1;
    while VarPart <> nil do
    begin
      I := VarPart.RecordSize;
      Dec(I, VarPart.Offset);
      if I > Size then
        Size := I;
      VarPart := VarPart.Next;
    end;
  end
  else if (Selector <> nil) and (Selector.Name <> '') then
    with Selector do
    begin
      Off := Offset;
      Size := FieldType.Size;
    end
  else if Members.Count > 0 then
    with TField(Members.Last) do
    begin
      Off := Offset;
      Size := FieldType.Size;
    end
  else
  begin
    Off := 0;
    Size := 1;
  end;
  if Off > $7fffffff then
    Result := Off
  else if Size > $7fffffff then
    Result := Size
  else
    Result := Off + int64(Size);
  Result := (Result + MaxAlignSize - 1) and not (MaxAlignSize - 1);
end;

procedure TRecordBody.Update(GlobalAlignSize: byte; Offset: cardinal);

  procedure UpdateField(F: TField; var Offset: cardinal);
  var
    AlSize: byte;
  begin
    if Offset > $7fffffff then
    begin
      F.Offset := Offset;
      Exit;
    end;
    AlSize := F.FieldType.AlignSize;
    if AlSize > GlobalAlignSize then
      AlSize := GlobalAlignSize;
    if AlSize > 1 then
      Offset := (Offset + AlSize - 1) and not (AlSize - 1);
    F.Offset := Offset;
    if F.FieldType.Size <= $7fffffff then
      Offset := Offset + F.FieldType.Size
    else
      Offset := F.FieldType.Size;
  end;

  procedure AlignTo(var Offset: cardinal; AlSize: byte);
  begin
    if AlSize > GlobalAlignSize then
      AlSize := GlobalAlignSize;
    Offset := (Offset + AlSize - 1) and not (AlSize - 1);
  end;

var
  I: integer;
  F: TField;
  VarPart: TRecordVariant;
begin
  for I := 0 to Members.Count - 1 do
  begin
    F := TField(Members[I]);
    UpdateField(F, Offset);
  end;
  if (Selector <> nil) and (Selector.Name <> '') then
    UpdateField(Selector, Offset);
  VarPart := Variants;
  if VarPart <> nil then
  begin
    AlignTo(Offset, VarPart.MaxAlignSize);
    while
      VarPart <> nil do
    begin
      VarPart.Update(GlobalAlignSize, Offset);
      VarPart.Offset := Offset;
      VarPart := VarPart.Next;
    end;
  end;
end;

procedure TRecordBody.UpdateAlign;
var
  I, Align: integer;
  VarPart: TRecordVariant;
begin
  VarPart := Variants;
  while VarPart <> nil do
  begin
    VarPart.UpdateAlign;
    VarPart := VarPart.Next;
  end;
  Align := 1;
  for I := 0 to Members.Count - 1 do
    with TField(Members[I]).FieldType do
      if AlignSize > Align then
        Align := AlignSize;
  if (Selector <> nil) and (Selector.Name <> '') then
    with Selector.FieldType do
      if AlignSize > Align then
        Align := AlignSize;
  MaxAlignSize := Align;
  Align := 1;
  VarPart := Variants;
  while
    VarPart <> nil do
  begin
    if VarPart.MaxAlignSize > Align then
      Align := VarPart.MaxAlignSize;
    VarPart := VarPart.Next;
  end;
  VarPart := Variants;
  while VarPart <> nil do
  begin
    VarPart.MaxAlignSize := Align;
    VarPart := VarPart.Next;
  end;
  if Align > MaxAlignSize then
    MaxAlignSize := Align;
end;

destructor TRecordVariant.Destroy;
begin
  Next.Free;
  inherited;
end;

procedure TRecordType.Add(Sym: TSymbol);
begin
  Symbols.Add(Sym);
end;

procedure TRecordType.AddSymbol(Sym: TSymbol);
begin
  if Sym.Parent <> nil then
    raise EASTError.CreateFmt(SErr_SymbolHasParent, [Sym.Name]);
  Sym.Parent := Self;
end;

constructor TRecordType.Create;
begin
  inherited Create;
  FTypeCode := typRecord;
  GlobalAlignSize := 1;
  Symbols := TSymbolTable.Create(Self);
end;

destructor TRecordType.Destroy;
begin
  Symbols.Free;
  Body.Free;
  inherited;
end;

function TRecordType.FindSymbol(const S: TSymString): TSymbol;
begin
  Result := Symbols.Find(S);
end;

function TRecordType.GetAlignSize: byte;
begin
  if Body <> nil then
    Result := Body.MaxAlignSize
  else
    Result := 1;
end;

procedure TRecordType.Update;
var
  i: integer;
  T: TType;
begin
  if Body <> nil then
  begin
    if GlobalAlignSize > 1 then
      UpdateAlign;
    Body.Update(GlobalAlignSize, 0);
    FSize := Body.RecordSize;
  end;
  for i := 0 to Symbols.Count - 1 do
  begin
    T := TField(Symbols[i]).FieldType;
    case T.TypeCode of
      typRecord:
      begin
        if staNeedInit in TRecordType(T).RecordAttr then
          Include(RecordAttr, staNeedInit);
        if staNeedFree in TRecordType(T).RecordAttr then
          Include(RecordAttr, staNeedFree);
      end;
      typArray:
      begin
        if staNeedInit in TArrayType(T).ArrayAttr then
          Include(RecordAttr, staNeedInit);
        if staNeedFree in TArrayType(T).ArrayAttr then
          Include(RecordAttr, staNeedFree);
      end;
      else
        if T.TypeCode in AutoInitTypes then
          Include(RecordAttr, staNeedInit);
        if T.TypeCode in AutoFreeTypes then
          Include(RecordAttr, staNeedFree);
    end;
  end;
end;

procedure TRecordType.UpdateAlign;
begin
  if Body <> nil then
    Body.UpdateAlign;
end;

procedure TClassIntfEntry.UpdateVmtEntry(Index: integer; AIntfMeth, AImplMeth: TMethod);
begin
  if (AIntfMeth.Parent.NodeKind <> nkType) or (TType(AIntfMeth.Parent).TypeCode <> typInterface) or
    not FIntfType.IsInheritedFrom(TInterfaceType(AIntfMeth.Parent)) then
    raise EASTError.Create('TClassIntfEntry.UpdateEntry: Parent mismatch');
  if Length(FEntries) = 0 then
    SetLength(FEntries, FIntfType.AllSymbols.Count);
  if (Index < 0) or (Index >= Length(FEntries)) then
    raise EASTError.Create('TClassIntfEntry.UpdateEntry: Index out of bound');
  FEntries[Index].IntfMethod := AIntfMeth;
  FEntries[Index].ImplMethod := AImplMeth;
end;

procedure TClassType.Add(Sym: TSymbol);
begin
  Symbols.Add(Sym);
end;

procedure TClassType.AddInterface(Intf: TInterfaceType);
var
  Entry: TClassIntfEntry;
begin
  CreateInterfaces;
  Entry := TClassIntfEntry.Create;
  Entry.FIntfType := Intf;
  FInterfaces.Add(Entry);
end;

procedure TClassType.AddSymbol(Sym: TSymbol);
begin
  if Sym.Parent <> nil then
    raise EASTError.CreateFmt(SErr_SymbolHasParent, [Sym.Name]);
  Sym.Parent := Self;
end;

procedure TClassType.ClearInterface;
var
  i: integer;
begin
  if FInterfaces = nil then
    Exit;
  for i := 0 to FInterfaces.Count - 1 do
    TObject(FInterfaces[i]).Free;
end;

constructor TClassType.Create;
begin
  inherited;
  FTypeCode := typClass;
  FSize := SizeOf(Pointer);
  GlobalAlignSize := 1;
  Symbols := TSymbolTable.Create(Self);
end;

procedure TClassType.CreateInterfaces;
begin
  if FInterfaces = nil then
    FInterfaces := TFPList.Create;
end;

destructor TClassType.Destroy;
begin
  ClearInterface;
  FInterfaces.Free;
  FAllSymbols.Free;
  Symbols.Free;
  FClassRef.Free;
  inherited;
end;

function TClassType.FindBaseSymbol(const S: TSymString): TSymbol;
begin
  if Base <> nil then
    Result := Base.FindSymbol(S)
  else
    Result := nil;
end;

function TClassType.FindCurSymbol(const S: TSymString): TSymbol;
begin
  Result := Symbols.Find(S);
end;

function TClassType.FindIntfEntry(AIntf: TInterfaceType): TClassIntfEntry;
var
  I: integer;
begin
  Result := nil;
  for I := 0 to Self.InterfaceCount - 1 do
  begin
    Result := Self.IntfEntries[I];
    if Result.IntfType = AIntf then
      Exit;
  end;
  if not Assigned(Result) and Assigned(Base) then
    Result := Base.FindIntfEntry(AIntf);
end;

function TClassType.FindSymbol(const S: TSymString): TSymbol;
var
  Base: TClassType;
begin
  Base := Self;
  while Base <> nil do
  begin
    Result := Base.FindCurSymbol(S);
    if Result <> nil then
      Exit;
    Base := Base.Base;
  end;
  Result := nil;
end;

function TClassType.GetAllSymbols: TSymbolTable;

  procedure AddSymbols(Typ: TClassType; SymTable: TSymbolTable);
  var
    I: integer;
    sym: TSymbol;
  begin
    if Typ.Base <> nil then
      AddSymbols(Typ.Base, SymTable);
    with SymTable do
      Capacity := Capacity + Typ.Symbols.Count;
    for I := 0 to Typ.Symbols.Count - 1 do
    begin
      sym := Typ.Symbols[I];
      if (sym.NodeKind = nkMethod) and (fmOvrldFlag in TMethod(sym).Modifiers) then
        SymTable.AddOvrld(TMethod(sym))
      else
        SymTable.Add(sym);
    end;
  end;

begin
  if not Assigned(FAllSymbols) then
  begin
    FAllSymbols := TSymbolTable.Create(nil);
    FAllSymbols.Capacity := 32;
    AddSymbols(Self, FAllSymbols);
  end;
  Result := FAllSymbols;
end;

function TClassType.GetClassRef: TClassRefType;
begin
  if FClassRef = nil then
  begin
    FClassRef := TClassRefType.Create;
    FClassRef.RefType := Self;
    FClassRef.FParent := Self.Parent;
    Include(FClassRef.Attr, saTemp);
    FClassRef.Name := '$' + Self.Name;
  end;
  Result := FClassRef;
end;

function TClassType.GetInterface(Index: integer): TInterfaceType;
begin
  Result := GetIntfEntry(Index).IntfType;
end;

function TClassType.GetInterfaceCount: integer;
begin
  if FInterfaces = nil then
    Result := 0
  else
    Result := FInterfaces.Count;
end;

function TClassType.GetInternalAddrOfIntf(i: integer): Pointer;
begin
  if FInterfaces = nil then
    Result := nil
  else
    Result := @TClassIntfEntry(FInterfaces[i]).IntfType;
end;

function TClassType.GetIntfEntry(Index: integer): TClassIntfEntry;
begin
  if FInterfaces = nil then
    raise EASTError.Create('TClassType.GetIntfEntry: Index out of bound');
  Result := TClassIntfEntry(FInterfaces[Index]);
end;

function TClassType.IsImplemented(AIntf: TInterfaceType): boolean;
var
  I: integer;
begin
  Result := False;
  for I := 0 to Self.InterfaceCount - 1 do
    if Self.Interfaces[I] = AIntf then
    begin
      Result := True;
      Break;
    end;
  if not Result and Assigned(Base) then
    Result := Base.IsImplemented(AIntf);
end;

function TClassType.IsInheritedFrom(ABase: TClassType): boolean;
var
  C: TClassType;
begin
  C := Self;
  while Assigned(C) and (C <> ABase) do
    C := C.Base;
  Result := C = ABase;
end;

function TClassType.RttiEnabled: boolean;
var
  Base: TClassType;
begin
  Base := Self;
  while Assigned(Base) and not (caRtti in Base.ClassAttr) do
    Base := Base.Base;
  Result := Base <> nil;
end;

procedure TClassType.Update(PtrSize: integer);
var
  MaxAlign: integer;

  procedure UpdateField(F: TField; var Offset: int64);
  var
    AlSize: byte;
  begin
    if Offset > $7fffffff then
    begin
      F.Offset := Offset;
      Exit;
    end;
    AlSize := F.FieldType.AlignSize;
    if MaxAlign < AlSize then
      MaxAlign := AlSize;
    if AlSize > GlobalAlignSize then
      AlSize := GlobalAlignSize;
    if AlSize > 1 then
      Offset := (Offset + AlSize - 1) and not (AlSize - 1);
    F.Offset := Offset;
    if F.FieldType.Size <= $7fffffff then
      Offset := Offset + F.FieldType.Size
    else
      Offset := F.FieldType.Size;
  end;

  procedure UpdateRootVmt(const Meth: TSymString; Index: integer);
  var
    Sym: TSymbol;
  begin
    Sym := FindCurSymbol(Meth);
    if Assigned(Sym) and (Sym.NodeKind = nkMethod) and (fmVirtual in TMethod(Sym).Modifiers) then
    begin
      TMethod(Sym).VTIndex := Index - ROOT_VMT_OFFSET;
      Vmt[Index] := TMethod(Sym);
    end;
  end;

var
  i, idx: integer;
  Offset: int64;
  Sym: TSymbol;
  Meth: TMethod;
begin
  if Base = nil then
  begin
    ObjectSize := PtrSize;
    VmtEntryCount := ROOT_VMT_OFFSET;
    SetLength(Vmt, VmtEntryCount);
    UpdateRootVmt('SafeCallException', 0);
    UpdateRootVmt('AfterConstruction', 1);
    UpdateRootVmt('BeforeDestruction', 2);
    UpdateRootVmt('Dispatch', 3);
    UpdateRootVmt('DefaultHandler', 4);
    UpdateRootVmt('NewInstance', 5);
    UpdateRootVmt('FreeInstance', 6);
    UpdateRootVmt('Destroy', 7);
    Exit;
  end
  else
    Offset := Base.ObjectSize;
  MaxAlign := 0;
  for i := 0 to Symbols.Count - 1 do
  begin
    Sym := Symbols[i];
    if Sym.NodeKind = nkField then
      UpdateField(TField(Sym), Offset);
  end;
  if InterfaceCount > 0 then
  begin
    Offset := (Offset + PtrSize - 1) and not (PtrSize - 1);
    for i := 0 to InterfaceCount - 1 do
    begin
      IntfEntries[i].FOffset := Offset;
      Offset := Offset + PtrSize;
    end;
  end;
  if MaxAlign > GlobalAlignSize then
    MaxAlign := GlobalAlignSize;
  if MaxAlign > 0 then
    ObjectSize := (Offset + MaxAlign - 1) and not (MaxAlign - 1)
  else
    ObjectSize := Offset;
  VmtEntryCount := Base.VmtEntryCount;
  for i := 0 to Symbols.Count - 1 do
  begin
    Sym := Symbols[i];
    if Sym.NodeKind = nkMethod then
    begin
      Meth := TMethod(Sym);
      if not (saStatic in Meth.Attr) and ([fmVirtual, fmOverride] * Meth.Modifiers = [fmVirtual]) then
      begin
        Meth.VTIndex := VmtEntryCount - ROOT_VMT_OFFSET;
        Inc(VmtEntryCount);
      end;
    end;
  end;
  SetLength(
    Vmt, VmtEntryCount);
  if VmtEntryCount > 0 then
  begin
    if Assigned(Base) and (Base.VmtEntryCount > 0) then
      Move(Base.Vmt[0], Self.Vmt[0], Base.VmtEntryCount * SizeOf(Pointer));
    for i := 0
      to Symbols.Count - 1 do
    begin
      Sym := Symbols[i];
      if Sym.NodeKind = nkMethod then
      begin
        Meth := TMethod(Sym);
        if not (saStatic in Meth.Attr) and (fmVirtual in Meth.Modifiers) then
        begin
          idx := Meth.VTIndex + ROOT_VMT_OFFSET;
          if (idx >= 0) and (idx < VmtEntryCount) then
            Vmt[idx] := Meth
          else
            Assert(False, 'Vmt index out of bound');
        end;
      end;
    end;
  end;
end;

constructor TSubrangeType.Create;
begin
  inherited;
  FTypeCode := typSubrange;
end;

procedure TSubrangeType.SetBaseType(const Value: TType);
begin
  if (Value <> nil) and not Value.IsOrdinal then
    raise EASTError.Create('Subrange must be an ordered type');
  FBaseType := Value;
  if FBaseType <> nil then
    Self.Size := FBaseType.Size;
end;

function TSubrangeType.SubSetOf(typ: TSubrangeType): boolean;
begin
  Result := (typ.RangeBegin <= Self.RangeBegin) and (typ.RangeEnd >= Self.RangeEnd);
end;

constructor TSetType.Create;
begin
  inherited;
  FTypeCode := typSet;
end;

function TSetType.GetAlignSize: byte;
begin
  if Size = 3 then
    Result := 4
  else if Size > 4 then
    Result := 1
  else
    Result := Size;
end;

function TSetType.IsCommonSetType: boolean;
begin
  Result :=
    RangeType = nil;
end;

procedure TSetType.Update;
begin
  if RangeType <> nil then
  begin
    FLowByte := RangeType.RangeBegin div 8;
    FHighByte := RangeType.RangeEnd div 8;
  end
  else
  begin
    FLowByte := 0;
    FHighByte := 31;
  end;
  UpdateSize;
end;

procedure TSetType.UpdateSize;
begin
  if RangeType <> nil then
  begin
    FSize := RangeType.RangeEnd div 8 - RangeType.RangeBegin div 8 + 1;
    if Size = 3 then
      FSize := 4;
  end
  else
    FSize := 32;
end;

constructor TClassRefType.Create;
begin
  inherited;
  FTypeCode := typClassRef;
  FSize := SizeOf(Pointer);
end;

function TClassRefType.IsInheritedFrom(ClassRef: TClassRefType): boolean;
begin
  if (Self.RefType <> nil) and (ClassRef.RefType <> nil) then
  begin
    Result := RefType.IsInheritedFrom(ClassRef.RefType);
  end
  else
    Result := False;
end;

constructor TIntfProperty.Create;
begin
  inherited;
  FNodeKind := nkIntfProperty;
end;

procedure TIntfProperty.CreateParams;
begin
  if Params = nil then
    Params := TFuncParamList.Create;
end;

destructor TIntfProperty.Destroy;
begin
  Params.Free;
  inherited;
end;

function TIntfProperty.ParamCount: integer;
begin
  if Params = nil then
    Result := 0
  else
    Result :=
      Params.Count;
end;

procedure TInterfaceType.Add(Sym: TSymbol);
begin
  Symbols.Add(Sym);
end;

procedure TInterfaceType.AddSymbol(Sym: TSymbol);
begin
  if Sym.Parent <> nil then
    raise EASTError.CreateFmt(SErr_SymbolHasParent, [Sym.Name]);
  Sym.Parent := Self;
end;

constructor TInterfaceType.Create;
begin
  inherited;
  FTypeCode := typInterface;
  FSize := SizeOf(Pointer);
  Symbols := TSymbolTable.Create(Self);
end;

destructor TInterfaceType.Destroy;
begin
  Symbols.Free;
  FAllSymbols.Free;
  inherited;
end;

function TInterfaceType.FindBaseSymbol(const S: TSymString): TSymbol;
begin
  if Base <> nil then
    Result := Base.FindSymbol(S)
  else
    Result := nil;
end;

function TInterfaceType.FindCurSymbol(const S: TSymString): TSymbol;
begin
  Result := Symbols.Find(S);
end;

function TInterfaceType.FindSymbol(const S: TSymString): TSymbol;
var
  Base: TInterfaceType;
begin
  Base := Self;
  while Base <> nil do
  begin
    Result := Base.FindCurSymbol(S);
    if Result <> nil then
      Exit;
    Base := Base.Base;
  end;
  Result := nil;
end;

function TInterfaceType.GetAllSymbols: TSymbolTable;

  procedure AddSymbols(Typ: TInterfaceType; SymTable: TSymbolTable);
  var
    I: integer;
    sym: TSymbol;
  begin
    if Typ.Base <> nil then
      AddSymbols(Typ.Base, SymTable);
    with
      SymTable do
      Capacity := Capacity + Typ.Symbols.Count;
    for I := 0 to Typ.Symbols.Count - 1 do
    begin
      sym := Typ.Symbols[I];
      if (sym.NodeKind = nkMethod) and (fmOvrldFlag in TMethod(sym).Modifiers) then
        SymTable.AddOvrld(TMethod(sym))
      else
        SymTable.Add(sym);
    end;
  end;

begin
  if not Assigned(FAllSymbols) then
  begin
    FAllSymbols := TSymbolTable.Create(nil);
    FAllSymbols.Capacity := 16;
    AddSymbols(Self, FAllSymbols);
  end;
  Result := FAllSymbols;
end;

function TInterfaceType.IsInheritedFrom(ABase: TInterfaceType): boolean;
var
  C: TInterfaceType;
begin
  C := Self;
  while Assigned(C) and (C <> ABase) do
    C := C.Base;
  Result := C = ABase;
end;

procedure TInterfaceType.UpdateVmt;
var
  i: integer;
  sym: TSymbol;
begin
  if Base = nil then
    VmtEntryCount := 0
  else
    VmtEntryCount := Base.VmtEntryCount;
  for i := 0 to Symbols.Count - 1 do
  begin
    sym := Symbols[i];
    if sym.NodeKind = nkMethod then
    begin
      TMethod(sym).VTIndex := VmtEntryCount;
      Inc(VmtEntryCount);
    end;
  end;
end;

procedure TObjectType.Add(Sym: TSymbol);
begin
  Symbols.Add(Sym);
end;

procedure TObjectType.AddSymbol(Sym: TSymbol);
begin
  if Sym.Parent <> nil then
    raise EASTError.CreateFmt(SErr_SymbolHasParent, [Sym.Name]);
  Sym.Parent := Self;
end;

constructor TObjectType.Create;
begin
  inherited;
  FTypeCode := typObject;
  Symbols :=
    TSymbolTable.Create(Self);
end;

destructor TObjectType.Destroy;
begin
  Symbols.Free;
  FAllSymbols.Free;
  inherited;
end;

function TObjectType.FindBaseSymbol(const S: TSymString): TSymbol;
begin
  if Base <> nil then
    Result := Base.FindSymbol(S)
  else
    Result := nil;
end;

function TObjectType.FindCurSymbol(const S: TSymString): TSymbol;
begin
  Result := Symbols.Find(S);
end;

function TObjectType.FindSymbol(const S: TSymString): TSymbol;
var
  Base: TObjectType;
begin
  Base := Self;
  while Base <> nil do
  begin
    Result := Base.FindCurSymbol(S);
    if Result <> nil then
      Exit;
    Base := Base.Base;
  end;
  Result := nil;
end;

function TObjectType.GetAllSymbols: TSymbolTable;

  procedure AddSymbols(Typ: TObjectType; SymTable: TSymbolTable);
  var
    I: integer;
    sym: TSymbol;
  begin
    if Typ.Base <> nil then
      AddSymbols(Typ.Base, SymTable);
    with SymTable do
      Capacity := Capacity + Typ.Symbols.Count;
    for I := 0 to Typ.Symbols.Count - 1 do
    begin
      sym := Typ.Symbols[I];
      if (sym.NodeKind = nkMethod) and (fmOvrldFlag in TMethod(sym).Modifiers) then
        SymTable.AddOvrld(TMethod(sym))
      else
        SymTable.Add(Typ.Symbols[I]);
    end;
  end;

begin
  if not Assigned(FAllSymbols) then
  begin
    FAllSymbols := TSymbolTable.Create(nil);
    FAllSymbols.Capacity := 32;
    AddSymbols(Self, FAllSymbols);
  end;
  Result := FAllSymbols;
end;

function TObjectType.IsInheritedFrom(ABase: TObjectType): boolean;
var
  C: TObjectType;
begin
  C := Self;
  while
    Assigned(C) and (C <> ABase) do
    C := C.Base;
  Result := C = ABase;
end;

procedure TObjectType.Update(PtrSize: integer);
var
  MaxAlign: integer;

  procedure UpdateField(F: TField; var Offset: int64);
  var
    AlSize: byte;
  begin
    if Offset > $7fffffff then
    begin
      F.Offset := Offset;
      Exit;
    end;
    AlSize := F.FieldType.AlignSize;
    if MaxAlign < AlSize then
      MaxAlign := AlSize;
    if AlSize > GlobalAlignSize then
      AlSize := GlobalAlignSize;
    if AlSize > 1 then
      Offset := (Offset + AlSize - 1) and not (AlSize - 1);
    F.Offset := Offset;
    if F.FieldType.Size <= $7fffffff then
      Offset :=
        Offset + F.FieldType.Size
    else
      Offset := F.FieldType.Size;
  end;

var
  i, BaseVmt: integer;
  Offset: int64;
  Sym: TSymbol;
begin
  if Assigned(Base) then
    BaseVmt := Base.VmtEntryCount
  else
    BaseVmt := 0;
  VmtEntryCount := BaseVmt;
  for i := 0 to Symbols.Count - 1 do
  begin
    Sym := Symbols[i];
    if not (saStatic in Sym.Attr) and (Sym.NodeKind = nkMethod) and
      ([fmVirtual, fmOverride] * TFunction(Sym).Modifiers = [fmVirtual]) then
    begin
      TMethod(Sym).VTIndex := VmtEntryCount;
      Inc(VmtEntryCount);
    end;
  end;
  if VmtEntryCount > BaseVmt then
    Include(ObjectAttr, oaHasVirtual);
  if oaHasVirtual in ObjectAttr then
    Include(ObjectAttr, oaHasVmt)
  else if (Base <> nil) and (oaHasVmt in Base.ObjectAttr) then
    Include(ObjectAttr, oaHasVmt);
  if Base = nil then
  begin
    if oaHasVmt in ObjectAttr then
      Include(ObjectAttr, oaBeginVmt);
  end
  else if oaHasVmt in ObjectAttr then
  begin
    if not (oaHasVmt in base.ObjectAttr) then
      Include(ObjectAttr, oaBeginVmt);
  end;
  if Base = nil then
    Offset := 0
  else
    Offset := Base.Size;
  MaxAlign := 0;
  for i := 0 to Symbols.Count - 1 do
  begin
    Sym := Symbols[i];
    if Sym.NodeKind = nkField then
      UpdateField(TField(Sym), Offset);
  end;
  if oaBeginVmt in ObjectAttr then
  begin
    Offset := (Offset + PtrSize - 1) and not (PtrSize - 1);
    VmtOffset := Offset;
    Offset := Offset + PtrSize;
  end;
  if MaxAlign > GlobalAlignSize then
    MaxAlign := GlobalAlignSize;
  if MaxAlign > 0 then
    FSize := (Offset + MaxAlign - 1) and not (MaxAlign - 1)
  else
    FSize := Offset;
  if FSize = 0 then
    FSize := 1;
end;

constructor TFileType.Create;
begin
  inherited;
  FTypeCode := typFile;
  FSize := SizeOf(Pointer);
end;

function TFileType.IsUntype: boolean;
begin
  Result := ElementType = nil;
end;

constructor TTextType.Create;
begin
  inherited;
  FTypeCode := typText;
  FSize := SizeOf(Pointer);
end;

constructor TProceduralType.Create;
begin
  inherited;
  FTypeCode := typProcedural;
  FSize := SizeOf(Pointer);
end;

procedure TProceduralType.CreateParams;
begin
  if Params = nil then
    Params := TFuncParamList.Create;
end;

destructor TProceduralType.Destroy;
begin
  Params.Free;
  inherited;
end;

function TProceduralType.MinOfParams: integer;
var
  I: integer;
begin
  Result := 0;
  if Params = nil then
    Exit;
  for I := 0 to Params.Count - 1 do
    if Params[I].DefaultValue.VT = vtEmpty then
      Inc(Result);
end;

function TProceduralType.ParamCount: integer;
begin
  if Params = nil then
    Result := 0
  else
    Result := Params.Count;
end;

constructor TSymbolType.Create;
begin
  inherited;
  FTypeCode := typSymbol;
end;

constructor TExpr.Create;
begin
  inherited Create;
  FNodeKind := nkExpr;
end;

procedure TExpr.Detach;
begin
  if FParent <> nil then
    FParent.Remove(Self);
end;

function TExpr.GetConstantSymbol: TConstant;
var
  Sym: TSymbol;
begin
  Sym := GetReference;
  if Sym.NodeKind = nkConstant then
    Result := TConstant(Sym)
  else
    Result := nil;
end;

function TExpr.GetFunctionSymbol: TFunctionDecl;
var
  Ref: TSymbol;
begin
  Ref := GetReference;
  if (Ref <> nil) and (Ref.NodeKind in [nkFunc, nkMethod, nkExternalFunc]) then
    Result := TFunctionDecl(Ref)
  else
    Result := nil;
end;

function TExpr.GetReference: TSymbol;
begin
  case OpCode of
    opSYMBOL: Result := TSymbolExpr(Self).Reference;
    opMEMBER: if TBinaryExpr(Self).Right <> nil then
        Result := TBinaryExpr(Self).Right.GetReference
      else
        Result := nil;
    else
      Result := nil;
  end;
end;

function TExpr.GetVariableSymbol: TVariable;
var
  Ref: TSymbol;
begin
  Ref := GetReference;
  if (Ref <> nil) and (Ref.NodeKind = nkVariable) then
    Result := TVariable(Ref)
  else
    Result := nil;
end;

function TExpr.HasMemory: boolean;
const
  ExpectedKinds = [nkField, nkFuncParam];
begin
  case OpCode of
    opSYMBOL:
    begin
      with
        TSymbolExpr(Self) do
        Result := (Reference.NodeKind in ExpectedKinds) or ((Reference.NodeKind = nkVariable) and
          not (vaSelf in TVariable(Reference).VarAttr));
    end;
    opMEMBER: if TBinaryExpr(Self).Right <> nil then
        Result := TBinaryExpr(Self).Right.HasMemory
      else
        Result := False;
    opINDEX: Result := TBinaryExpr(Self).Left.HasMemory;
    opINST: Result := True;
    opCAST: Result := eaVarCast in Self.Attr;
    else
      Result := False;
  end;
end;

function TExpr.IsCharConstant: boolean;
var
  LRef: TSymbol;
  LTyp: TType;
begin
  Result := False;
  LRef := Self.GetReference;
  if (LRef <> nil) and (LRef.NodeKind = nkConstant) then
    LTyp := TConstant(LRef).ConstType
  else
  if Self.OpCode = opCONST then
    LTyp := Self.Typ
  else
    Exit;
  Result := (LTyp.TypeCode = typChar);
end;

function TExpr.IsClassType: boolean;
var
  Sym: TSymbol;
begin
  Sym := GetReference;
  if Sym <> nil then
    Result := (Sym.NodeKind = nkType) and (TType(Sym).TypeCode = typClass)
  else
    Result := False;
end;

function TExpr.IsConstantValue: boolean;
begin
  case OpCode of
    opNIL, opCONST: Result := True;
    opSYMBOL: Result := GetReference.NodeKind = nkConstant;
    else
      Result := False;
  end;
end;

function TExpr.IsCtorCall: boolean;
var
  Fun: TFunctionDecl;
begin
  Result := Self.OpCode = opCALL;
  if Result then
  begin
    Fun := TBinaryExpr(Self).Left.GetFunctionSymbol;
    Result := (Fun <> nil) and (Fun.NodeKind = nkMethod) and (TMethod(Fun).MethodKind = mkConstructor);
  end;
end;

function TExpr.IsCtorSymbol: boolean;
var
  Fun: TFunctionDecl;
begin
  Fun := Self.GetFunctionSymbol;
  Result := (Fun <> nil) and (Fun.NodeKind = nkMethod) and (TMethod(Fun).MethodKind = mkConstructor);
end;

function TExpr.IsEmptyString: boolean;

  function IsEmptyVal(const V: TValueRec): boolean;
  begin
    Result := (V.VT = vtEmpty) or ((V.VT in [vtStr, vtWStr]) and (ansistring(V.VStr) = ''));
  end;

var
  Sym: TSymbol;
begin
  Result := False;
  case OpCode of
    opSYMBOL:
    begin
      Sym := TSymbol(TSymbolExpr(Self).Reference);
      if Sym.NodeKind = nkConstant then
        Result :=
          IsEmptyVal(TConstant(Sym).Value);
    end;
    opConst:
    begin
      Result := IsEmptyVal(TConstExpr(Self).Value);
    end;
  end;
end;

function TExpr.IsFunction: boolean;
begin
  Result := Self.GetFunctionSymbol <> nil;
end;

function TExpr.IsNilConst: boolean;
begin
  Result := (Self.OpCode = opNIL);
end;

function TExpr.IsStringConstant: boolean;
var
  Ref: TSymbol;
  LTyp: TType;
begin
  Result :=
    False;
  Ref := Self.GetReference;
  if (Ref <> nil) and (Ref.NodeKind = nkConstant) then
    LTyp := TConstant(Ref).ConstType
  else if Self.OpCode = opCONST then
    LTyp := Self.Typ
  else
    Exit;
  Result :=
    (LTyp.TypeCode = typString);
end;

function TExpr.IsTypedConstant: boolean;
var
  Ref: TSymbol;
begin
  Ref := Self.GetReference;
  Result := (Ref <> nil) and (Ref.NodeKind = nkVariable) and (vaReadOnly in TVariable(Ref).VarAttr);
end;

function TExpr.IsTypeSymbol: boolean;
var
  Sym: TSymbol;
begin
  Sym := Self.GetReference;
  if Sym <> nil then
    Result := Sym.NodeKind = nkType
  else
    Result := False;
end;

procedure TExpr.Remove(Child: TExpr);
begin
end;

procedure TExpr.Reset;
begin
  Self.Next := nil;
  Self.FParent := nil;
  Self.Attr := [];
  Self.Switches := [];
  Self.Typ := nil;
end;

procedure TExpr.SetReference(Ref: TSymbol);
begin
  case OpCode of
    opSYMBOL: TSymbolExpr(Self).Reference := Ref;
    opMEMBER: if TBinaryExpr(Self).Right <> nil then
        TBinaryExpr(Self).Right.SetReference(Ref);
  end;
end;

procedure TUnaryExpr.Remove(Child: TExpr);
begin
  if FOperand = Child then
  begin
    FOperand := nil;
    Child.FParent := nil;
  end;
end;

procedure TUnaryExpr.Reset;
begin
  inherited;
  FOperand := nil;
end;

procedure TUnaryExpr.SetOperand(const Value: TExpr);
begin
  if FOperand = Value then
    Exit;
  if (Value <> nil) and (Value.Parent <> nil) then
    raise EASTError.Create('expr has in use');
  if FOperand <> nil then
    FOperand.FParent :=
      nil;
  FOperand := Value;
  if FOperand <> nil then
    FOperand.FParent := Self;
end;

procedure TBinaryExpr.Remove(Child: TExpr);
begin
  if FLeft = Child then
  begin
    FLeft := nil;
    Child.FParent := nil;
  end
  else if FRight = Child then
  begin
    FRight := nil;
    Child.FParent := nil;
  end;
end;

procedure TBinaryExpr.Reset;
begin
  inherited;
  FLeft := nil;
  FRight := nil;
end;

procedure TBinaryExpr.SetLeft(const Value: TExpr);
begin
  if Value = FLeft then
    Exit;
  if (Value <> nil) and (Value.Parent <> nil) then
    Value.Parent.Remove(Value);
  if FLeft <> nil then
    FLeft.FParent := nil;
  FLeft := Value;
  if FLeft <> nil then
    FLeft.FParent := Self;
end;

procedure TBinaryExpr.SetRight(const Value: TExpr);
begin
  if Value = FRight then
    Exit;
  if (Value <> nil) and (Value.Parent <> nil) then
    Value.Parent.Remove(Value);
  if FRight <> nil then
    FRight.FParent := nil;
  ;
  FRight := Value;
  if FRight <> nil then
    FRight.FParent := Self;
end;

procedure TListExpr.Add(E: TExpr);
begin
  if E.Parent = Self then
    raise EASTError.Create('expr is in use');
  if Count >= Length(Items) then
    SetLength(Items, Count + 4);
  Items[Count] := E;
  Inc(Count);
  if Assigned(E.Parent) then
    E.Parent.Remove(E);
  E.FParent := Self;
end;

constructor TListExpr.Create;
begin
  inherited Create;
  OpCode := opLIST;
end;

procedure TListExpr.Delete(Index: integer);
var
  i: integer;
begin
  if (Index < 0) or (Index >= Count) then
    raise EAStError.Create('Index out of bound');
  Items[Index].FParent := nil;
  for i := Index + 1 to Count - 1 do
    Items[i - 1] := Items[i];
  Dec(Count);
end;

function TListExpr.IndexOf(E: TExpr): integer;
var
  I: integer;
begin
  for i := 0 to Self.Count - 1 do
    if Items[i] = E then
    begin
      Result := i;
      Exit;
    end;
  Result := -1;
end;

procedure TListExpr.Insert(Index: integer; E: TExpr);
var
  i: integer;
begin
  if E.Parent = Self then
    raise EASTError.Create('expr is in use');
  if (Index < 0) or (Index > Count) then
    raise EASTError.Create('Index out of bound');
  if Count >= Length(Items) then
    SetLength(Items, Count + 4);
  Inc(Count);
  for i := Index + 1 to Count - 1 do
    Items[i] := Items[i - 1];
  Items
    [Index] := E;
  if E.Parent <> nil then
    E.Parent.Remove(E);
  E.FParent := Self;
end;

procedure TListExpr.Remove(E: TExpr);
var
  i: integer;
begin
  for i := 0 to Self.Count - 1 do
    if Items[i] = E then
    begin
      Delete(i);
      Exit;
    end;
end;

procedure TListExpr.Replace(Index: integer; E: TExpr);
begin
  if (Index < 0) or (Index >= Count) then
    raise EASTError.Create('Index out of bound');
  if Items[Index] = E then
    Exit;
  Items[Index].FParent := nil;
  Items[Index] := E;
  if E.Parent <> nil then
    E.Parent.Remove(E);
  E.FParent := Self;
end;

procedure TListExpr.Reset;
begin
  inherited Reset;
  Self.Count := 0;
end;

procedure TListExpr.SetCapacity(Num: integer);
begin
  if Num < Count then
    Exit;
  SetLength(Items, Num);
end;

destructor TConstExpr.Destroy;
begin
  ValClear(Value);
  inherited;
end;

procedure TConstExpr.Reset;
begin
  inherited;
  ValClear(Value);
end;

procedure TSymbolExpr.Reset;
begin
  inherited;
  Self.Reference := nil;
  Self.
    Name := '';
end;

procedure TStrConstExpr.Reset;
begin
  inherited;
  RawValue := '';
end;

constructor TEmptyStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skEmptyStmt;
end;

constructor TCompoundStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skCompoundStmt;
  Statements := TFPList.Create;
end;

destructor TCompoundStmt.Destroy;
begin
  Statements.Free;
  inherited;
end;

constructor TCallStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skCallStmt;
end;

constructor TLabeledStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skLabelStmt;
end;

constructor TStmtLabel.Create;
begin
  inherited;
  FNodeKind := nkLabel;
end;

constructor TAssignmentStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skAssignmentStmt;
end;

constructor TIfStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skIfStmt;
end;

constructor TForStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skForStmt;
end;

constructor TWhileStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skWhileStmt;
end;

procedure TCaseSelector.AddRange(Start, Stop: int64);
begin
  if FCount >= Length(Values) then
    SetLength(Values, Length(Values) + 4);
  Values[FCount].Start := Start;
  Values[FCount].Stop := Stop;
  Inc(FCount);
end;

procedure TCaseSelector.
Clear;
begin
  FCount := 0;
end;

function TCaseSelector.Contains(Start, Stop: int64): boolean;
var
  i: integer;
begin
  for i := 0 to FCount - 1 do
    if not ((Start > Values[i].Stop) or (Stop < Values[i].Start)) then
    begin
      Result := True;
      Exit;
    end;
  Result := False;
end;

destructor TCaseSelector.Destroy;
begin
  Clear;
  inherited;
end;

function TCaseSelector.TotalValueCount: int64;
var
  i: integer;
begin
  Result := 0;
  for i := 0 to FCount - 1 do
  begin
    Inc(Result, Values[i].Stop - Values[i].Start + 1);
  end;
end;

procedure TCaseStmt.AddSelector(Selector: TCaseSelector);
begin
  if FCount >= Length(Selectors) then
    SetLength(Selectors, Length(Selectors) + 4);
  Selectors[FCount] := Selector;
  Inc(FCount);
end;

procedure TCaseStmt.Clear;
var
  I: integer;
begin
  for I := 0 to Count - 1 do
  begin
    Selectors[I].Free;
    Selectors[I] := nil;
  end;
end;

function TCaseStmt.Contains(Start, Stop: int64): boolean;
var
  I: integer;
begin
  for I := 0 to Count - 1 do
  begin
    Result := Selectors[I].Contains(Start, Stop);
    if Result then
      Exit;
  end;
  Result := False;
end;

constructor TCaseStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skCaseStmt;
end;

destructor TCaseStmt.Destroy;
begin
  Clear;
  inherited;
end;

function TCaseStmt.TotalValueCount: int64;
var
  I: integer;
begin
  Result := 0;
  for I := 0 to Count - 1 do
  begin
    Inc(Result, Selectors[I].TotalValueCount);
  end;
end;

constructor TRepeatStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skRepeatStmt;
end;

constructor TGotoStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skGotoStmt;
end;

procedure TFunctionDecl.AddOverload(Func: TFunctionDecl);
var
  F: TFunctionDecl;
begin
  F := Self;
  while
    F.NextOverload <> nil do
    F := F.NextOverload;
  F.NextOverload := Func;
  Include(Func.Modifiers, fmOvrldFlag);
end;

procedure TFunctionDecl.CreateParams;
begin
  if Params = nil then
    Params := TFuncParamList.Create;
end;

procedure TFunctionDecl.CreateProceduralType;
begin
  FProcType := TProceduralType.Create;
  if Self.Params <> nil then
  begin
    FProcType.CreateParams;
    FProcType.Params.Copy(Self.Params);
  end;
  FProcType.ReturnType := Self.ReturnType;
  FProcType.CallConvention := Self.CallConvention;
  FProcType.Parent := Self.Parent;
  Include(FProcType.Attr, saTemp);
end;

destructor TFunctionDecl.Destroy;
begin
  Params.Free;
  FProcType.Free;
  inherited;
end;

function TFunctionDecl.GetProceduralType: TProceduralType;
begin
  if not Assigned(FProcType) then
    CreateProceduralType;
  Result := FProcType;
end;

function TFunctionDecl.IsOverload: boolean;
begin
  Result := (NextOverload <> nil) and (fmOverload in Self.Modifiers);
end;

function TFunctionDecl.MinOfParams: integer;
var
  I: integer;
begin
  Result := 0;
  if Params = nil then
    Exit;
  for I := 0 to Params.Count - 1 do
    if Params[I].DefaultValue.VT = vtEmpty then
      Inc(Result);
end;

function TFunctionDecl.ParamCount: integer;
begin
  if Params = nil then
    Result := 0
  else
    Result := Params.Count;
end;

constructor TExternalFunction.Create;
begin
  inherited;
  FNodeKind := nkExternalFunc;
end;

procedure TFunction.Add(Sym: TSymbol);
begin
  LocalSymbols.Add(Sym);
end;

procedure TFunction.AddSymbol(Sym: TSymbol);
begin
  if not (Sym.NodeKind in [nkType, nkLabel, nkEnumElement, nkVariable, nkConstant, nkFunc, nkFuncParam]) then
    raise EASTError.Create('Node kind invalid for function');
  if Sym.Parent = nil then
    Sym.Parent := Self
  else if Sym.Parent <> Self then
    raise EASTError.CreateFmt(SErr_SymbolHasParent, [Sym.Name]);
end;

constructor TFunction.Create;
begin
  inherited;
  FNodeKind := nkFunc;
  LocalSymbols := TSymbolTable.Create(Self);
  LocalSymbols.Capacity :=
    16;
end;

destructor TFunction.Destroy;
begin
  LocalSymbols.Free;
  Codes.Free;
  inherited;
end;

constructor TMethod.Create;
begin
  inherited;
  FNodeKind := nkMethod;
end;

procedure TMethod.CreateProceduralType;
begin
  inherited;
  FProcType.IsMethodPointer := not (fmStatic in Self.Modifiers);
  FProcType.MethodKind := Self.MethodKind;
  FProcType.ObjectKind := Self.ObjectKind;
end;

function TMethod.IsClassOrStatic: boolean;
begin
  Result := (saStatic in Self.Attr) or (saClass in Self.Attr);
end;

constructor TMethodResolution.Create;
begin
  inherited;
  FNodeKind := nkMethodResolution;
end;

constructor TBuiltinFunction.Create;
begin
  inherited;
  FNodeKind := nkBuiltinFunc;
end;

constructor TEnumValue.Create;
begin
  inherited;
  FNodeKind := nkEnumElement;
end;

constructor TVariable.Create;
begin
  inherited;
  FNodeKind := nkVariable;
end;

destructor TVariable.Destroy;
begin
  ValClear(Value);
  inherited;
end;

constructor TConstant.Create;
begin
  inherited;
  FNodeKind := nkConstant;
end;

destructor TConstant.Destroy;
begin
  ValClear(Value);
  inherited;
end;

class function TSetValue.Add(L, R: TSetValue): TSetValue;
var
  I: integer;
begin
  Result := TSetValue.Create;
  Result.BitStart := Min(L.BitStart, R.BitStart);
  Result.BitCount := Max(L.BitCount, R.BitCount);
  for I := 0
    to 31 do
    Result.Bits[I] := L.Bits[I] or R.Bits[I];
end;

procedure TSetValue.Assign(Source: TSetValue);
begin
  Self.BitStart := Source.BitStart;
  Self.BitCount := Source.BitCount;
  Move(Source.Bits, Self.Bits, SizeOf(Self.Bits));
end;

{$push}
{$warn 5094 off}
function TSetValue.AsString: string;
const
  digits: array[0..15] of char = ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F');
var
  i, j: integer;
begin
  SetLength(Result, Length(Bits) * 2);
  j := 1;
  for
    i := Low(Bits) to High(Bits) do
  begin
    Result[j] := Digits[(Bits[i] shr 4) and $0F];
    Result
      [j + 1] := Digits[Bits[i] and $0F];
    Inc(j, 2);
  end;
end;
{$pop}

constructor TSetValue.Create;
begin
  BitStart := 255;
end;

function TSetValue.Equal(R: TSetValue): boolean;
var
  I: integer;
begin
  Result := (BitStart = R.BitStart) and (BitCount = R.BitCount);
  if Result then
    for I := Low(Bits) to High(Bits) do
    begin
      Result := Bits[I] = Bits[I];
      if not Result then
        Exit;
    end;
end;

function TSetValue.Include(R: TSetValue): boolean;
var
  I: integer;
  L, H: integer;
begin
  L := Min(BitStart, R.BitStart) div 8;
  H := Max(BitCount, R.BitCount) div 8;
  Result := False;
  for I := L to H do
  begin
    Result := (not Bits[I] and R.Bits[I]) = 0;
    if not Result then
      Exit;
  end;
end;

function TSetValue.IsEmpty: boolean;
begin
  Result := BitCount = 0;
end;

function TSetValue.MinSize: integer;
begin
  Result := (BitStart + BitCount) div 8 - BitStart div 8 + 1;
  if Result = 3 then
    Result := 4;
end;

class function TSetValue.Mul(L, R: TSetValue): TSetValue;
var
  I: integer;
begin
  Result := TSetValue.Create;
  Result.BitStart := Min(L.BitStart, R.BitStart);
  Result.BitCount := Max(L.BitCount, R.BitCount);
  for I := 0 to 31 do
    Result.Bits[I] := L.Bits[I] and R.Bits[I];
end;

procedure TSetValue.SetBits(Index: byte; Value: boolean);
var
  I, Offset: integer;
begin
  I := Index div 8;
  Offset := Index mod 8;
  if Value then
    Bits[I] := Bits[I] or (1 shl Offset)
  else
    Bits[I] := Bits[I] and not (1 shl Offset);
end;

procedure TSetValue.
SetRange(Lo, Hi: byte; Value: boolean);
var
  i: integer;
begin
  for i := Lo to Hi do
    SetBits(i, Value);
end;

class function TSetValue.Sub(L, R: TSetValue): TSetValue;
var
  I: integer;
begin
  Result := TSetValue.Create;
  Result.BitStart := Min(L.BitStart, R.BitStart);
  Result.BitCount := Max(L.BitCount, R.BitCount);
  for I := 0 to 31 do
    Result.Bits[I] := L.Bits[I] and (not R.Bits[I]);
end;

function TSetValue.TestBits(Index: byte): boolean;
var
  I, Offset: integer;
begin
  I := Index div 8;
  Offset := Index mod 8;
  Result := (Bits[I] and (1 shl Offset)) <> 0;
end;

procedure TSetValue.Update;
const
  _bits: array[0..7] of byte = (1, 2, 4, 8, 16, 32, 64, 128);

  function _bit_start(b: byte): integer;
  var
    I: integer;
  begin
    for I := 0 to 7 do
      if b and _bits[I] <> 0 then
      begin
        Result := I;
        Exit;
      end;
    Result := 0;
  end;

  function _bit_start_rev(b: byte): integer;
  var
    I: integer;
  begin
    for I := 7 downto 0 do
      if b and _bits[I] <> 0 then
      begin
        Result := I;
        Exit;
      end;
    Result := 0;
  end;

var
  I, H, L: integer;
begin
  BitStart := 0;
  BitCount := 0;
  H := -1;
  L := -1;
  for I := 0 to High(Bits) do
    if Bits[I] <> 0 then
    begin
      L := I;
      Break;
    end;
  if L = -1 then
    Exit;
  for I := High(Bits) downto 0 do
    if Bits[I] <> 0 then
    begin
      H := I;
      Break;
    end;
  BitStart := L * 8 + _bit_start(Bits[L]);
  I := H * 8 + _bit_start_rev(Bits[H]);
  BitCount := I - BitStart + 1;
end;

procedure TArrayValue.Assign(Source: TArrayValue);
var
  i: integer;
begin
  Self.FElementCount := Source.FElementCount;
  Self.FElementType := Source.FElementType;
  Self.FBounds := Source.FBounds;
  Items := AllocMem(FElementCount);
  for i := 0 to FElementCount - 1 do
  begin
    ValCopy(Items[i], Source.Items[i]);
  end;
end;

procedure TArrayValue.Clear;
var
  i: integer;
begin
  for i := 0 to FElementCount - 1 do
    ValClear(Items[i]);
  Items := nil;
  FBounds := nil;
  FElementType := nil;
  FElementCount := 0;
end;

procedure TArrayValue.CreateValue(typ: TArrayType);
var
  i: integer;
  LCount: int64;
begin
  SetLength(FBounds, typ.DimensionCount);
  for i := 0 to Length(FBounds) - 1 do
  begin
    LCount := typ.Range.RangeEnd - typ.Range.RangeBegin + 1;
    FBounds[i] := LCount;
    if typ.ElementType.TypeCode = typArray then
      typ := TArrayType(typ.ElementType);
  end;
  FElementType := typ.ElementType;
  FElementCount := GetElementCount;
  LCount := SizeOf(TValueRec) * int64(FElementCount);
  if LCount > MaxInt then
    Assert(False, 'Array too large');
  SetLength(Items, FElementCount);
end;

destructor TArrayValue.Destroy;
begin
  Clear;
  inherited;
end;

function TArrayValue.GetDimCount: integer;
begin
  Result := Length(FBounds);
end;

function TArrayValue.GetElementCount: integer;
var
  i: integer;
begin
  Result := 0;
  if Length(Bounds) > 0 then
  begin
    Result := Bounds[0];
    for i := 1 to High(Bounds) do
      Result := Result * Bounds[i];
  end;
end;

function TArrayValue.Put(Index: integer; var V: TValueRec): boolean;
begin
  Assert((Index >= 0) and (Index < FElementCount), 'Out of index in Put');
  Result := ValIsCompatible(V, FElementType);
  if Result then
  begin
    case FElementType.TypeCode of
      typRecord:
      begin
        ValClear(Items[Index]);
        Items[Index].VT := V.VT;
        Items[Index].VRecord := V.VRecord;
        V.VT := vtEmpty;
      end;
      typSet:
      begin
        ValClear(Items[Index]);
        Items[Index].VT := V.VT;
        Items[Index].VSet := V.VSet;
        V.VT := vtEmpty;
      end;
      else
        ValCopy(Items[Index], V);
    end;
  end;
end;

procedure TRecordValue.Assign(Source: TRecordValue);
var
  i: integer;
begin
  FType := Source.FType;
  FElementCount := Source.FElementCount;
  SetLength(Items, Length(Source.Items));
  for i :=
    0 to Length(Items) - 1 do
    ValCopy(Items[i], Source.Items[i]);
end;

procedure TRecordValue.Clear;
var
  I: integer;
begin
  for I := 0 to Length(Items) - 1 do
    ValClear(Items[I]);
  Items := nil;
  FType := nil;
  FElementCount := 0;
end;

procedure TRecordValue.CreateValue(typ: TRecordType);
begin
  FType := typ;
  FElementCount := typ.Symbols.Count;
  SetLength(Items, FElementCount);
end;

destructor TRecordValue.Destroy;
begin
  Clear;
  inherited;
end;

function TRecordValue.Put(Index: integer; var V: TValueRec): boolean;
var
  typ: TType;
begin
  Assert((Index >= 0) and (Index < FElementCount), 'Out of index in Put');
  typ := TField(FType.Symbols.Item[Index]).FieldType;
  Result := ValIsCompatible(V, typ);
  if Result then
  begin
    case typ.TypeCode of
      typArray:
      begin
        ValClear(Items[Index]);
        Items[Index].VT := V.VT;
        Items[Index].VArray := V.VArray;
        V.VT := vtEmpty;
      end;
      typRecord:
      begin
        ValClear(Items[Index]);
        Items[Index].
          VT := V.VT;
        Items[Index].VRecord := V.VRecord;
        V.VT := vtEmpty;
      end;
      typSet:
      begin
        ValClear(Items[Index]);
        Items[Index].VT := V.VT;
        Items[Index].VSet := V.VSet;
        V.VT := vtEmpty;
      end;
      else
        ValCopy(Items[Index], V);
    end;
  end;
end;

constructor TFuncParam.Create;
begin
  inherited;
  FNodeKind := nkFuncParam;
end;

destructor TFuncParam.Destroy;
begin
  ValClear(DefaultValue);
  inherited;
end;

function TFuncParam.IsReadOnly: boolean;
begin
  Result := argConst = Modifier;
end;

procedure TFuncParamList.Add(P: TFuncParam);
begin
  if FCount = Length(FItems) then
    SetLength(FItems, FCount + 4);
  FItems[FCount] := P;
  Inc(FCount);
end;

procedure TFuncParamList.Copy(Source: TFuncParamList);
var
  i: integer;
begin
  FCount := Source.Count;
  SetLength(FItems, FCount);
  for i := 0 to FCount - 1 do
    FItems[i] := Source.Items[i];
end;

function TFuncParamList.Get(Index: integer): TFuncParam;
begin
  if (Index < 0) or (Index >= FCount) then
    raise Classes.EListError.CreateFmt('TFuncParamList.Get: Index %d out of bound', [Index]);
  Result := FItems[Index];
end;

function TFuncParamList.GetCapacity: integer;
begin
  Result := Length(FItems);
end;

procedure TFuncParamList.SetCapacity(Value: integer);
begin
  if Value > Length(FItems) then
    SetLength(FItems, Value);
end;

procedure TFuncParamList.SetCount(Value: integer);
begin
  if Value < 0 then
    Value := 0
  else if Value > Length(FItems) then
    Value := Length(FItems);
  FCount := Value;
end;

procedure TExceptBlock.AddExceptHandler(Block: TExceptHandler);
begin
  if FCount >= Length(ExceptHandlers) then
    SetLength(ExceptHandlers, FCount + 4);
  ExceptHandlers[FCount] := Block;
  Inc(FCount);
end;

procedure TExceptBlock.Clear;
var
  I: integer;
begin
  for I := 0 to FCount - 1 do
    Self.ExceptHandlers[I].Free;
  Self.ExceptHandlers := nil;
end;

destructor TExceptBlock.Destroy;
begin
  Clear;
  inherited;
end;

constructor TTryStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skTryStmt;
end;

destructor TTryStmt.Destroy;
begin
  ExceptBlock.Free;
  inherited;
end;

function TTryStmt.IsFinallyOrExcept(S: TStatement): boolean;
var
  i: integer;
begin
  Result := Self.FinallyStmt = S;
  if not Result and Assigned(ExceptBlock) then
  begin
    for i := 0 to ExceptBlock.Count - 1 do
      if ExceptBlock.ExceptHandlers[i].Stmt = S then
      begin
        Result := True;
        Exit;
      end;
  end;
end;

constructor TRaiseStmt.Create;
begin
  inherited;
  FNodeKind := nkStmt;
  FStmtKind := skRaiseStmt;
  Include(Attr, stmtNoreturn);
end;

function TSymbolTable.Add(Sym: TSymbol): boolean;
var
  hc: cardinal;
begin
  hc := HashOfStr(Sym.Name);
  Result := inherited IsExists(PChar(Sym.Name), hc);
  inherited PutStr(Sym.Name, hc, Sym);
  if FAutoAddToOwner and (Owner <> nil) then
    Owner.AddSymbol(Sym);
end;

function TSymbolTable.AddOvrld(Sym: TFunctionDecl): boolean;
var
  hc: cardinal;
  s: string;
begin
  s := Format('%s@%d', [Sym.Name, Sym.ID]);
  hc := HashOfStr(s);
  Result := inherited IsExists(PChar(s), hc);
  inherited PutStr(s, hc, Sym);
end;

procedure TSymbolTable.Clear(FreeSym: boolean);
var
  i: integer;
begin
  if FreeSym then
    for i := 0 to Count - 1 do
      Self.Item[i].Free;
  inherited
  Clear;
end;

constructor TSymbolTable.Create(AOwner: TSymbol);
begin
  inherited Create(
    0, False);
  FOwner := AOwner;
  FAutoAddToOwner := True;
end;

function TSymbolTable.Find(M: TModule; const S: TSymString): TSymbol;
var
  P: PPHashItem;
begin
  if M = nil then
  begin
    Result := Find(S);
    Exit;
  end;
  P := inherited Lookup(PChar(S));
  while P^ <> nil do
  begin
    if (TSymbol(P^.Value).Module = M) and SameText(string(P^.Key), S) then
    begin
      Result := TSymbol(P^.Value);
      Exit;
    end
    else
      P := @P^.Next;
  end;
  Result := nil;
end;

function TSymbolTable.Find(const S: TSymString): TSymbol;
begin
  Result := TSymbol(inherited Get(PChar(S)));
end;

function TSymbolTable.GetNext(var Pos: TSymbolPosition): TSymbol;
begin
  Result := FindNext(Pos);
end;

function TSymbolTable.GetStart(const S: TSymString): TSymbolPosition;
begin
  Result := FindFirst(PChar(S));
end;

function TSymbolTable.GetSymbol(Index: integer): TSymbol;
begin
  Result := TSymbol(inherited ValueByIndex(Index));
end;

initialization
  InitDirectives;

finalization
  _Directives.Free;
  _Directives := nil;
end.
