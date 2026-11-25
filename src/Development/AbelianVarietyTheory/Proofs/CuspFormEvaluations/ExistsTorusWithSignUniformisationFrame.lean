module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndRaw
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusSign

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := GlobalTheory.AnVal.halfIntegralGenerator_trace_eq_one H

theorem exists_torusAt_of_isom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {r : ℕ} (X : FD.Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)))
    (x : FD.Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ A : I2.TorusAt X x, A.w0 = H.w0 := by
  have key : ∀ a b, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)) = -((D.EF a b : ℤ) : ℚ) := by
    intro a b
    rw [isom, neg_mul, map_neg, neg_neg]
  refine GlobalTheory.torusAtExists E r X ?_ H.w0 ?_ x hx
  · intro f
    obtain ⟨a, ha⟩ := D.unimod.2 (-(f.comp φ.toLinearMap.toAddMonoidHom).toIntLinearMap)
    refine ⟨φ a, (φ a).2, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := φ.surjective v
    rw [key, ha]
    simp
  · intro u hu v hv
    obtain ⟨a, ha⟩ := φ.surjective ⟨u, hu⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨v, hv⟩
    have hu' : u = (φ a : Fin r → E) := by rw [ha]
    have hv' : v = (φ b : Fin r → E) := by rw [hb]
    have hw : H.w0 - H.bar H.w0 = 1 - (H.bar H.w0 + H.bar H.w0) := by
      have := cmHostUnit_add_conj_eq_one H
      linear_combination this
    have hs : ((H.w0 : E) - FD.cc (H.w0 : E)) • v = (φ ((H.w0 - H.bar H.w0) • b) : Fin r → E) := by
      rw [map_smul, hb, FD.cc, ← H.bar_eq]
      funext i
      simp [Algebra.smul_def]
    refine ⟨D.EF a (H.bar H.w0 • b), ?_⟩
    rw [hs, hu', hv', key, key, hw, sub_smul, add_smul, one_smul, map_sub, map_add (f := _)]
    push_cast
    ring

theorem exists_torusAt_w0_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W
  exact exists_torusAt_of_isom (W.F.Di (W.ik k)) (U.X k) (W.φ k) (W.isom k) x.1 x.2

end GlobalTheory.TorusSign
