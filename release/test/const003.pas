(*
<test>
  <description>Constant check (real to/from int conversion error)</description>
  <command>%%pc %%source -E </command>
  <expect>
    <output action="contains">(1218)</output>
  </expect>
</test>
*)
unit const003;

interface

const
    c1 = 25.5;
    c2 = Longint(c1);

implementation

end.
