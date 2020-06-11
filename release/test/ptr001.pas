(*
<test>
  <description>
    pointer assignment bug
  </description>
  <command>%%pc -E %%source </command>
  <expect>
    <exitcode>0</exitcode>
  </expect>
</test>
*)
unit ptr001;

{$mode delphi}
interface

function test(var p: PPointer; var intf: IInterface): Pointer;

implementation

function test(var p: PPointer; var intf: IInterface): Pointer;
begin
	result := @p;
	result := @intf;
end;

end.
