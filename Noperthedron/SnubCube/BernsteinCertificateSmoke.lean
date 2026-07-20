module

public import Noperthedron.SnubCube.BernsteinCertificate
public meta import Noperthedron.SnubCube.BernsteinCertificate

@[expose] public section


namespace Noperthedron.SnubCube.BernsteinCertificateSmoke

open BernsteinCertificate
open SparseTribonacciPolynomial
open TribonacciExpr

def linearTable : Table 1 where
  degrees := ![1]
  coefficient := fun index => if index 0 = 0 then ofRat 1 else ofRat 2
  indices := [![0], ![1]]

def linearPolynomial : Polynomial 1 := 1 + var 0

theorem linearTable_complete_kernel : linearTable.Complete := by
  decide +kernel

theorem linearTable_complete_native : linearTable.Complete := by
  native_decide

theorem linearTable_represents_kernel :
    linearTable.Represents linearPolynomial := by
  decide +kernel

theorem linearTable_represents_native :
    linearTable.Represents linearPolynomial := by
  native_decide

theorem linearTable_lower_kernel : linearTable.LowerValid 1 := by
  decide +kernel

theorem linearTable_lower_native : linearTable.LowerValid 1 := by
  native_decide

theorem linearPolynomial_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 : ℝ) ≤ evalReal ![x] linearPolynomial := by
  have h := linearTable.lower_le_polynomial linearPolynomial 1 (values := ![x])
    linearTable_complete_kernel linearTable_represents_kernel
    (fun i => by fin_cases i; simpa using And.intro hx0 hx1)
    linearTable_lower_kernel
  norm_num at h
  exact h

end Noperthedron.SnubCube.BernsteinCertificateSmoke

end
