module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibresStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfDiv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbMulFlat

open FibreFlat FiniteFibreFlat


set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : LocallyQuasiFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := PositivityTheory.HtPt.Twhopf.flat_of_flatOver_fields f g hY h0 h1 h2 H

theorem flat_and_locallyQuasiFinite_pow :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 →
      Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  intro S G _ _ hG n hn
  change Flat (Out.mulA G n).left ∧ LocallyQuasiFinite (Out.mulA G n).left
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm := AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (Out.mulA G n).left := QuasiCompact.of_comp _ G.hom
  have hq : LocallyQuasiFinite (Out.mulA G n).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [IntDiv.comp_mulA]
      exact HomExt.finite_torsion_points hG t (Nat.pos_of_ne_zero hn)
  refine ⟨flat_of_flatOver_fields _ G.hom inferInstance (by rw [Over.w]; infer_instance)
    (by rw [Over.w]; infer_instance) hq fun k _ t => ?_, hq⟩
  exact flatOver_of_pullback _ _ (IntDiv.flat_fibre G _ k t)

end GlobalTheory.SemiAbMulFlat
