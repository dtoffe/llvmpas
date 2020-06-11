(*
<test>
  <description>Classes without constructors are generated and passed to the same type of parameters</description>
  <command>%%pc -E %%source </command>
  <expect>
    <exitcode>0</exitcode>
  </expect>
</test>
*)
program ctor005;
{$mode delphi}

type
	tmyobj = class
	end;

procedure test(obj: tmyobj);
begin
	obj.free;
end;

begin
	test( tmyobj.create );
end.
