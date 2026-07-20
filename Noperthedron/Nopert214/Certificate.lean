module

public import Noperthedron.BalancedSupport.RationalCertificate
public import Noperthedron.Nopert214.Vertices

@[expose] public section


/-!
# Balanced-global certificates for Nopert #214

The checker is the generic rational balanced-support checker instantiated
with the exact rational Nopert #214 vertices.  Since the formal vertices are
rational, the real/rational approximation error is identically zero.
-/

namespace Noperthedron.Nopert214.Certificate

abbrev Contact :=
  Noperthedron.BalancedSupport.RationalCertificate.Contact VertexIndex
abbrev Box :=
  Noperthedron.BalancedSupport.RationalCertificate.Box VertexIndex

def Box.Valid (box : Box) : Prop :=
  Noperthedron.BalancedSupport.RationalCertificate.Box.Valid
    rationalPolyhedron box

instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem Box.valid_imp_not_translated_rupert (box : Box) (h : box.Valid) :
    ∀ q, Pose.near box.center.toReal (box.εα : ℝ) (box.εθ₁ : ℝ)
        (box.εφ₁ : ℝ) (box.εθ₂ : ℝ) (box.εφ₂ : ℝ) q →
      ∀ offset : ℝ²,
        ¬ RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull := by
  exact Noperthedron.BalancedSupport.RationalCertificate.Box.valid_imp_not_translated_rupert
    exactGoodPoly rationalPolyhedron exactApproximation box h

theorem Box.valid_imp_no_translated_rupert_in_interval
    (box : Box) (h : box.Valid) :
    ¬ ∃ q ∈ box.realInterval, ∃ offset : ℝ²,
      RupertPose (q.matrixPoseWithOffset offset) exactGoodPoly.hull := by
  exact Noperthedron.BalancedSupport.RationalCertificate.Box.valid_imp_no_translated_rupert_in_interval
    exactGoodPoly rationalPolyhedron exactApproximation box h

end Noperthedron.Nopert214.Certificate

end
