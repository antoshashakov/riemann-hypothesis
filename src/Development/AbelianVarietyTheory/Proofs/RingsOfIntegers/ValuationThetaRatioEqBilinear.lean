module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatioVal

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

def germConst (F : Type) [Field F] (z : Spec (CommRingCat.of F)) : F →+* (Spec (CommRingCat.of F)).presheaf.stalk z :=
  ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem gs_specMap {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F))
    (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ a = germConst F z (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a)) := by
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Spec (CommRingCat.of F)).presheaf.germ ⊤ z trivial).hom (appTop_specMap (CommRingCat.ofHom f) a)

theorem gs_id_const {F : Type} [Field F] (z : Spec (CommRingCat.of F)) (c : F) :
    gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) = germConst F z c := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem gs_scal {A F : Type} [CommRing A] [Field F] (f : A →+* F) (z : Spec (CommRingCat.of F)) (c : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ (scal (𝟙 (Spec (CommRingCat.of A))) c) = germConst F z (f c) := by
  rw [gs_specMap]
  congr 2
  simp [scal]

theorem unit_calc {S : Type} [CommRing S] {s G τ C P R E Eψ Er fam u : Sˣ} {T c₀ cψ cr A : S} {k : ℕ}
    (h1 : s.val = T * G.val) (h2 : τ * C = s ^ k) (h3 : fam = τ * (P * R)) (h4 : fam.val = c₀ * E.val)
    (h5 : P.val = cψ * Eψ.val) (h6 : R.val = cr * Er.val) (h8 : u.val = A)
    (hu : u = E * Eψ⁻¹ * Er⁻¹ * C * (G ^ k)⁻¹) : c₀ * A = T ^ k * cψ * cr := by
  have e1 : u * (Eψ * Er * G ^ k) = E * C := by
    rw [hu]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have e2 : fam * C = s ^ k * (P * R) := by rw [h3, ← h2]; ac_rfl
  have e1' := congrArg Units.val e1
  have e2' := congrArg Units.val e2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, h1, h4, h5, h6, h8, mul_pow] at e1' e2'
  apply (Eψ * Er * G ^ k).isUnit.mul_right_cancel
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  linear_combination c₀ * e1' + e2'

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem v_ratio_gt (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {k : ℕ} (hk : 1 ≤ k) (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = p.g.b)
    (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)) (hG₀ : G₀.IsGen) (t : F)
    (ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
        (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) :
    ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = QForm.bOf D.toPre Q p.y α := by
  first
  | exact _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.v_ratio_gt
  | (apply _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.v_ratio_gt <;> assumption)

theorem main : TWM.VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

end GlobalTheory.RatioVal
