{-------------------------------------------------------------------------------

  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at http://mozilla.org/MPL/2.0/.

-------------------------------------------------------------------------------}
{===============================================================================

  MD4 Hash Calculation

  ©František Milt 2015-03-15

  Version 1.1

===============================================================================}
unit MD4;

{$DEFINE LargeBuffer}
{.$DEFINE UseStringStream}

interface

uses
  Classes;

type
{$IFDEF x64}
  TSize = UInt64;
{$ELSE}
  TSize = LongWord;
{$ENDIF}

  TMD4Hash = Record
    PartA:  LongWord;
    PartB:  LongWord;
    PartC:  LongWord;
    PartD:  LongWord;
  end;
  PMD4Hash = ^TMD4Hash;

const
  InitialMD4: TMD4Hash = (
    PartA:  $67452301;
    PartB:  $EFCDAB89;
    PartC:  $98BADCFE;
    PartD:  $10325476);

  ZeroMD4: TMD4Hash = (PartA: 0; PartB: 0; PartC: 0; PartD: 0);

Function MD4toStr(Hash: TMD4Hash): String;
Function StrToMD4(Str: String): TMD4Hash;
Function TryStrToMD4(const Str: String; out Hash: TMD4Hash): Boolean;
Function StrToMD4Def(const Str: String; Default: TMD4Hash): TMD4Hash;
Function SameMD4(A,B: TMD4Hash): Boolean;

procedure BufferMD4(var Hash: TMD4Hash; const Buffer; Size: TSize); overload;
Function LastBufferMD4(Hash: TMD4Hash; const Buffer; Size: TSize; MessageSize: Int64 = -1): TMD4Hash;

Function BufferMD4(const Buffer; Size: TSize): TMD4Hash; overload;

Function AnsiStringMD4(const Str: AnsiString): TMD4Hash;
Function WideStringMD4(const Str: WideString): TMD4Hash;
Function StringMD4(const Str: String): TMD4Hash;

Function StreamMD4(Stream: TStream; Count: Int64 = -1): TMD4Hash;
Function FileMD4(const FileName: String): TMD4Hash;

//------------------------------------------------------------------------------

type
  TMD4Context = type Pointer;

Function MD4_Init: TMD4Context;
procedure MD4_Update(Context: TMD4Context; const Buffer; Size: TSize);
Function MD4_Final(var Context: TMD4Context; const Buffer; Size: TSize): TMD4Hash; overload;
Function MD4_Final(var Context: TMD4Context): TMD4Hash; overload;
Function MD4_Hash(const Buffer; Size: TSize): TMD4Hash;


implementation

uses
  SysUtils, Math;

const
  ChunkSize       = 64;                           // 512 bits
{$IFDEF LargeBuffers}
  ChunksPerBuffer = 16384;                        // 1MiB BufferSize
{$ELSE}
  ChunksPerBuffer = 64;                           // 4KiB BufferSize
{$ENDIF}
  BufferSize      = ChunksPerBuffer * ChunkSize;  // size of read buffer

  ShiftCoefs: Array[0..47] of LongWord = (
    3,  7, 11, 19,  3,  7, 11, 19,  3,  7, 11, 19,  3,  7, 11, 19,
    3,  5,  9, 13,  3,  5,  9, 13,  3,  5,  9, 13,  3,  5,  9, 13,
    3,  9, 11, 15,  3,  9, 11, 15,  3,  9, 11, 15,  3,  9, 11, 15);

  RoundConsts: Array[0..2] of LongWord = ($0, $5A827999, $6ED9EBA1);

  IndexConsts: Array[0..47] of LongWord = (
    0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    0,  4,  8, 12,  1,  5,  9, 13,  2,  6, 10, 14,  3,  7, 11, 15,
    0,  8,  4, 12,  2, 10,  6, 14,  1,  9,  5, 13,  3, 11,  7, 15);

type
  TChunkBuffer = Array[0..ChunkSize - 1] of Byte;

  TMD4Context_Internal = record
    MessageHash:    TMD4Hash;
    MessageSize:    Int64;
    TransferSize:   LongWord;
    TransferBuffer: TChunkBuffer;
  end;
  PMD4Context_Internal = ^TMD4Context_Internal;

//==============================================================================

Function LeftRotate(Number,Shift: LongWord): LongWord; register; {$IFNDEF PurePascal}assembler;{$ENDIF}
{$IFDEF PurePascal}
begin
  Result := (Number shl Shift) or (Number shr (32 - Shift));
end;
{$ELSE}
{$IFDEF FPC}{$ASMMODE intel}{$ENDIF}
asm
{$IFDEF x64}
  MOV   EAX,  ECX
{$ENDIF}
  MOV   CL,   DL
  ROL   EAX,  CL
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function ChunkHash(Hash: TMD4Hash; const Chunk): TMD4Hash;
var
  i:              Integer;
  Temp:           LongWord;
  FuncResult:     LongWord;
  RoundConstant:  LongWord;
  ChunkWords:     Array[0..15] of LongWord absolute Chunk;
begin
Result := Hash;
For i := 0 to 47 do
  begin
    case i of
       0..15: begin
                FuncResult := (Hash.PartB and Hash.PartC) or ((not Hash.PartB) and Hash.PartD);
                RoundConstant := RoundConsts[0];
              end;
      16..31: begin
                FuncResult := (Hash.PartB and Hash.PartC) or (Hash.PartB and Hash.PartD) or (Hash.PartC and Hash.PartD);
                RoundConstant := RoundConsts[1];
              end;
    else
      {32..47:} FuncResult := Hash.PartB xor Hash.PartC xor Hash.PartD;
                RoundConstant := RoundConsts[2];
    end;
    Temp := Hash.PartD;
    Hash.PartD := Hash.PartC;
    Hash.PartC := Hash.PartB;
    Hash.PartB := LeftRotate(Hash.PartA + FuncResult + ChunkWords[IndexConsts[i]] + RoundConstant, ShiftCoefs[i]);
    Hash.PartA := Temp;
  end;
Inc(Result.PartA,Hash.PartA);
Inc(Result.PartB,Hash.PartB);
Inc(Result.PartC,Hash.PartC);
Inc(Result.PartD,Hash.PartD);
end;

//==============================================================================

Function MD4toStr(Hash: TMD4Hash): String;
var
  HashArray:  Array[0..15] of Byte absolute Hash;
  i:          Integer;
begin
Result := StringOfChar('0',32);
For i := Low(HashArray) to High(HashArray) do
  begin
    Result[(i * 2) + 2] := IntToHex(HashArray[i] and $0F,1)[1];
    Result[(i * 2) + 1] := IntToHex(HashArray[i] shr 4,1)[1];
  end;
end;

//------------------------------------------------------------------------------

Function StrToMD4(Str: String): TMD4Hash;
var
  HashArray:  Array[0..15] of Byte absolute Result;
  i:          Integer;
begin
If Length(Str) < 32 then
  Str := StringOfChar('0',32 - Length(Str)) + Str
else
  If Length(Str) > 32 then
    Str := Copy(Str,Length(Str) - 31,32);
For i := 0 to 15 do
  HashArray[i] := StrToInt('$' + Copy(Str,(i * 2) + 1,2));
end;

//------------------------------------------------------------------------------

Function TryStrToMD4(const Str: String; out Hash: TMD4Hash): Boolean;
begin
try
  Hash := StrToMD4(Str);
  Result := True;
except
  Result := False;
end;
end;

//------------------------------------------------------------------------------

Function StrToMD4Def(const Str: String; Default: TMD4Hash): TMD4Hash;
begin
If not TryStrToMD4(Str,Result) then
  Result := Default;
end;

//------------------------------------------------------------------------------

Function SameMD4(A,B: TMD4Hash): Boolean;
begin
Result := (A.PartA = B.PartA) and (A.PartB = B.PartB) and
          (A.PartC = B.PartC) and (A.PartD = B.PartD);
end;

//==============================================================================

procedure BufferMD4(var Hash: TMD4Hash; const Buffer; Size: TSize);
type
  TChunksArray = Array[0..0] of TChunkBuffer;
var
  i:  Integer;
begin
If (Size mod ChunkSize) = 0 then
  begin
    For i := 0 to Pred(Size div ChunkSize) do
      Hash := ChunkHash(Hash,TChunksArray(Buffer)[i]);
  end
else raise Exception.CreateFmt('BufferMD4: Buffer size is not divisible by %d.',[ChunkSize]);
end;

//------------------------------------------------------------------------------

Function LastBufferMD4(Hash: TMD4Hash; const Buffer; Size: TSize; MessageSize: Int64 = -1): TMD4Hash;
type
  TInt64Array = Array[0..0] of Int64;
var
  FullChunks:     Integer;
  LastChunkSize:  Integer;
  HelpChunks:     Integer;
  HelpChunksBuff: Pointer;
begin
Result := Hash;
If MessageSize < 0 then MessageSize := Size;
FullChunks := Size div ChunkSize;
If FullChunks > 0 then BufferMD4(Result,Buffer,FullChunks * ChunkSize);
LastChunkSize := Size - TSize(FullChunks * ChunkSize);
HelpChunks := Ceil((LastChunkSize + SizeOf(Int64) + 1) / ChunkSize);
HelpChunksBuff := AllocMem(HelpChunks * ChunkSize);
try
  Move(TByteArray(Buffer)[FullChunks * ChunkSize],HelpChunksBuff^,LastChunkSize);
  TByteArray(HelpChunksBuff^)[LastChunkSize] := $80;
  TInt64Array(HelpChunksBuff^)[HelpChunks * (ChunkSize div SizeOf(Int64)) - 1] := MessageSize * 8;
  BufferMD4(Result,HelpChunksBuff^,HelpChunks * ChunkSize);
finally
  FreeMem(HelpChunksBuff,HelpChunks * ChunkSize);
end;
end;

//==============================================================================

Function BufferMD4(const Buffer; Size: TSize): TMD4Hash;
begin
Result := LastBufferMD4(InitialMD4,Buffer,Size);
end;

//==============================================================================

Function AnsiStringMD4(const Str: AnsiString): TMD4Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamMD4(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferMD4(PAnsiChar(Str)^,Length(Str) * SizeOf(AnsiChar));
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function WideStringMD4(const Str: WideString): TMD4Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamMD4(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferMD4(PWideChar(Str)^,Length(Str) * SizeOf(WideChar));
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function StringMD4(const Str: String): TMD4Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamMD4(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferMD4(PChar(Str)^,Length(Str) * SizeOf(Char));
end;
{$ENDIF}

//==============================================================================

Function StreamMD4(Stream: TStream; Count: Int64 = -1): TMD4Hash;
var
  Buffer:       Pointer;
  BytesRead:    Integer;
  MessageSize:  Int64;
begin
If Assigned(Stream) then
  begin
    If Count = 0 then
      Count := Stream.Size - Stream.Position;
    If Count < 0 then
      begin
        Stream.Position := 0;
        Count := Stream.Size;
      end;
    MessageSize := Count;
    GetMem(Buffer,BufferSize);
    try
      Result := InitialMD4;
      repeat
        BytesRead := Stream.Read(Buffer^,Min(BufferSize,Count));
        If BytesRead < BufferSize then
          Result := LastBufferMD4(Result,Buffer^,BytesRead,MessageSize)
        else
          BufferMD4(Result,Buffer^,BytesRead);
        Dec(Count,BytesRead);
      until BytesRead < BufferSize;
    finally
      FreeMem(Buffer,BufferSize);
    end;
  end
else raise Exception.Create('StreamMD4: Stream is not assigned.');
end;

//------------------------------------------------------------------------------

Function FileMD4(const FileName: String): TMD4Hash;
var
  FileStream: TFileStream;
begin
FileStream := TFileStream.Create(FileName, fmOpenRead or fmShareDenyWrite);
try
  Result := StreamMD4(FileStream);
finally
  FileStream.Free;
end;
end;

//==============================================================================

Function MD4_Init: TMD4Context;
begin
Result := AllocMem(SizeOf(TMD4Context_Internal));
with PMD4Context_Internal(Result)^ do
  begin
    MessageHash := InitialMD4;
    MessageSize := 0;
    TransferSize := 0;
  end;
end;

//------------------------------------------------------------------------------

procedure MD4_Update(Context: TMD4Context; const Buffer; Size: TSize);
var
  FullChunks:     Integer;
  RemainingSize:  TSize;
begin
with PMD4Context_Internal(Context)^ do
  begin
    If TransferSize > 0 then
      begin
        If Size >= (ChunkSize - TransferSize) then
          begin
            Inc(MessageSize,ChunkSize - TransferSize);
            Move(Buffer,TransferBuffer[TransferSize],ChunkSize - TransferSize);
            BufferMD4(MessageHash,TransferBuffer,ChunkSize);
            RemainingSize := Size - (ChunkSize - TransferSize);
            TransferSize := 0;
            MD4_Update(Context,TByteArray(Buffer)[Size - RemainingSize],RemainingSize);
          end
        else
          begin
            Inc(MessageSize,Size);
            Move(Buffer,TransferBuffer[TransferSize],Size);
            Inc(TransferSize,Size);
          end;  
      end
    else
      begin
        Inc(MessageSize,Size);
        FullChunks := Size div ChunkSize;
        BufferMD4(MessageHash,Buffer,FullChunks * ChunkSize);
        If TSize(FullChunks * ChunkSize) < Size then
          begin
            TransferSize := Size - TSize(FullChunks * ChunkSize);
            Move(TByteArray(Buffer)[Size - TransferSize],TransferBuffer,TransferSize);
          end;
      end;
  end;
end;

//------------------------------------------------------------------------------

Function MD4_Final(var Context: TMD4Context; const Buffer; Size: TSize): TMD4Hash;
begin
MD4_Update(Context,Buffer,Size);
Result := MD4_Final(Context);
end;

//------------------------------------------------------------------------------

Function MD4_Final(var Context: TMD4Context): TMD4Hash;
begin
with PMD4Context_Internal(Context)^ do
  Result := LastBufferMD4(MessageHash,TransferBuffer,TransferSize,MessageSize);
FreeMem(Context,SizeOf(TMD4Context_Internal));
Context := nil;
end;

//------------------------------------------------------------------------------

Function MD4_Hash(const Buffer; Size: TSize): TMD4Hash;
begin
Result := LastBufferMD4(InitialMD4,Buffer,Size);
end;

end.
