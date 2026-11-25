module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

lemma rso_zeta_ne_near_one : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 1 → riemannZeta w ≠ 0 := by
  have h := riemannZeta_residue_one.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with w hw hw1 hz
  exact hw hw1 (by rw [hz, mul_zero])

lemma rso_deriv_zeta_diff : DifferentiableOn ℂ (deriv riemannZeta) {w : ℂ | w ≠ 1} := by
  have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
    fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
  exact hd.deriv isOpen_ne

lemma rso_Fy_diff (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta) w :=
    rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)
  have hd2 : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta h1
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd3 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) w :=
    (differentiableAt_id).const_cpow (Or.inl hy0)
  have hden : w * (w - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  unfold Fy
  exact (((hd1.div hd2 hz).neg).mul hd3).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hden

open Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.ZeroFreeDirichlet in
theorem rectangleShiftOfResidue : RectShiftOf := by
  intro _ _ y hy σ₁ σ₀ T hσ₁ hσ₁1 hσ₀ hT hzero
  let χ : DirichletCharacter ℂ 1 := 1
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hn (w : ℂ) (hw₁ : σ₁ ≤ w.re) (hw₂ : w.re ≤ σ₀) (hwT : |w.im| ≤ T) : exLF χ w ≠ 0 := by
    intro hw
    have hwne : w ≠ 1 := fun he => exLF_one_ne_zero χ (he ▸ hw)
    exact hzero w hw₁ hw₂ hwT hwne (by simpa only [hL] using (exLF_eq_zero_iff χ hwne).mp hw)
  have hmem (w : ℂ) : w ∈ (∅ : Finset ℂ) ↔ exLF χ w = 0 ∧ σ₁ < w.re ∧ |w.im| < T := by
    refine ⟨fun h => (Finset.notMem_empty _ h).elim, ?_⟩
    rintro ⟨hz, hr, hi⟩
    exact (hn w hr.le ((exLF_re_lt_one χ hz).trans hσ₀).le hi.le hz).elim
  have hedge (w : ℂ) (hw₁ : σ₁ ≤ w.re) (hw₂ : w.re ≤ σ₀) (hwT : |w.im| ≤ T)
      (hw : exLF χ w = 0) : σ₁ < w.re ∧ |w.im| < T :=
    (hn w hw₁ hw₂ hwT hw).elim
  have hex : exLF χ = riemannZeta₁ := by
    funext z
    change exLF (1 : DirichletCharacter ℂ 1) z = _
    by_cases hz : z = 1
    · simp [hz, exLF_one_char, DirichletCharacter.LFunctionTrivChar₁]
    · rw [exLF_one_char_apply hz, DirichletCharacter.LFunction_modOne_eq,
        riemannZeta_eq_inv_sub_mul hz, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz)]
  have hk : Fchi χ y = Fy y := by
    funext z
    unfold Fchi Fy negLD
    rw [hL]
  have hc : explicitFormulaConstant χ = -(Real.eulerMascheroniConstant : ℂ) := by
    unfold explicitFormulaConstant
    rw [hex, deriv_riemannZeta₁_one, riemannZeta₁_one, div_one]
  have h := ex_rect_Fchi χ y hy σ₁ σ₀ T hσ₁ hσ₁1 hσ₀ hT ∅ hmem hedge
  rw [hk, hc, ite_eq_left (show χ = 1 from rfl), Finset.sum_empty, sub_zero] at h
  linear_combination h

end Formalism.ZF
