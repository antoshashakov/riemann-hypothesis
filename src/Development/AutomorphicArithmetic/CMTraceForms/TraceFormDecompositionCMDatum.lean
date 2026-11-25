module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicArithmetic.CMTraceForms.Places
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.Norm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

namespace UpperTheory.TraceSumEquivalence

private theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) :=
  GlobalTheory.EmbCount.exists_equiv E C v O hv

private theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    have hadd : LinearMap.mulLeft ℤ_[p] (a + b) = LinearMap.mulLeft ℤ_[p] a + LinearMap.mulLeft ℤ_[p] b := by
      ext z
      simp [add_mul]
    rw [hadd, map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, ← Finset.sum_add_distrib]
    simp [map_add (f := _)]
  | tmul c y =>
    have h0 : (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) = c • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h1 : LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) =
        c • (Algebra.lmul ℤ (𝓞 E) y).baseChange ℤ_[p] := by
      rw [Algebra.baseChange_lmul, h0]
      ext z
      simp [smul_mul_assoc]
    have h2 : LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        c * ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℤ_[p]) := by
      rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul, Algebra.trace_apply]
      simp
    have h3 : ∑ σ : E →ₐ[ℚ] C, σ (y : E) = (((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) : C) := by
      rw [Algebra.coe_trace_int, ← eq_ratCast (algebraMap ℚ C), trace_eq_sum_embeddings]
    rw [h2]
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul]
    have h4 : ∀ σ : E →ₐ[ℚ] C, algebraMap O C ((Φ σ).toIntAlgHom y) = σ (y : E) := fun σ => hΦ σ y
    simp only [h4, Algebra.ofId_apply, ← Finset.mul_sum, h3, map_intCast, Rat.cast_intCast]

end UpperTheory.TraceSumEquivalence


open UpperTheory.TraceSumEquivalence in
theorem UpperTheory.trace_form_decomposition_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e →
      Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  apply GlobalTheory.EmbCount.card_emb <;> assumption
