module

public import Noperthedron.SnubCube.BernsteinCertificate
public meta import Noperthedron.SnubCube.BernsteinCertificate

@[expose] public section


namespace Noperthedron.SnubCube.BernsteinCertificateSmoke

open BernsteinCertificate
open TribonacciExpr

def linearTable : Table 1 where
  degrees := ![1]
  coefficient := fun index => if index 0 = 0 then ofRat 1 else ofRat 2

theorem linearTable_lower_kernel : linearTable.LowerValid 1 := by
  decide +kernel

theorem linearTable_lower_native : linearTable.LowerValid 1 := by
  native_decide

end Noperthedron.SnubCube.BernsteinCertificateSmoke

end
