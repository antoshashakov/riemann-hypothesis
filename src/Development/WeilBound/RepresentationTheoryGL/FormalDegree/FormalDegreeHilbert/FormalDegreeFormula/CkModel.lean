module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CkModel
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.ModelFunctionsMultiply
import Aesop.Frontend.Tactic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd.CkM

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

theorem blkMinor_diag_mul (ε : Fin n → Bool) (c : Fin n) (d : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    blkMinor ε c (diagonal d * X) =
      (∏ q ∈ univ.filter (fun q : Fin n => ε q = ε c ∧ q ≤ c), d q) * blkMinor ε c X := by
  exact _root_.CompanionTheory.RgFd.CkM.blkMinor_diag_mul ε c d X

theorem model_function_diag_mul (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (d : Fin n → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    f0 ε m (diagonal d * X) = (∏ a, d a ^ (m a).toNat) * f0 ε m X := by
  exact _root_.CompanionTheory.RgFd.CkM.model_function_diag_mul ε hm d X

theorem vsp_diag {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    (y : KG ε) (d : Fin n → ℂ) (hy : toMK y = diagonal d) (x : KG ε) :
    f (y * x) = (∏ a, d a ^ (m a).toNat) * f x := by
  exact _root_.CompanionTheory.RgFd.CkM.vsp_diag hm hf y d hy x

def ev (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m →ₗ[ℂ] ℂ := (LinearMap.proj (1 : KG ε)).comp (mvFnL ε m)

theorem ev_apply {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : ev ε m f = f.fn 1 := rfl

theorem cpart1_Eaa (ε : Fin n → Bool) (a : Fin n) : cpart1 ε (bdPart ε (single a a (1 : ℂ))) = 0 := by
  ext i j
  rw [cpart1_bdPart_apply]
  by_cases h : ε i = ε j
  · rw [if_pos h]
    simp only [single_apply]
    split_ifs <;> aesop
  · simp [h]

theorem cpart2_Eaa (ε : Fin n → Bool) (a : Fin n) :
    cpart2 ε (bdPart ε (single a a (1 : ℂ))) = (-Complex.I) • single a a (1 : ℂ) := by
  exact _root_.CompanionTheory.RgFd.CkM.cpart2_Eaa ε a

theorem exp_Eaa (a : Fin n) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • ((-Complex.I) • single a a (1 : ℂ))) =
      diagonal (fun c => if c = a then Complex.exp (-(Complex.I * t)) else 1) := by
  exact _root_.CompanionTheory.RgFd.CkM.exp_Eaa a t

theorem ev_dTau_Eaa {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) (f : MV ε m) :
    ev ε m (dTau ε m (single a a 1) f) = ((m a : ℤ) : ℂ) * ev ε m f := by
  apply CompanionTheory.RgFd.CkM.ev_dTau_Eaa <;> assumption

theorem model_op {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (k : KG ε) :
    (modelKType ε hm).op k = tauC ε m k := rfl

theorem model_dτ {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    (modelKType ε hm).dτ = dTau ε m := rfl

theorem model_w {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) : (modelKType ε hm).w = wN ε m := rfl

def uEv (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m :=
  (InnerProductSpace.toDual ℂ (MV ε m)).symm (LinearMap.toContinuousLinearMap (ev ε m))

theorem inner_uEv {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : ⟪uEv ε m, f⟫_ℂ = ev ε m f := by
  rw [uEv, InnerProductSpace.toDual_symm_apply]
  rfl

theorem uEv_wt {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (single a a 1) (uEv ε m) = (((m a : ℤ) : ℝ) : ℂ) • uEv ε m := by
  refine ext_inner_right ℂ fun f => ?_
  have hU := KType.kUnit (modelKType ε hm) a a rfl (uEv ε m) f
  simp only [kunits, model_dτ, ContinuousLinearMap.coe_coe] at hU
  have hU' : ⟪dTau ε m (single a a 1) (uEv ε m), f⟫_ℂ = ⟪uEv ε m, dTau ε m (single a a 1) f⟫_ℂ := hU
  rw [hU', inner_uEv, ev_dTau_Eaa hm, inner_smul_left, inner_uEv]
  simp

theorem not_cone_neg_root {a b : Fin n} (hab : a < b) (c : Fin n → Fin n → ℕ) (hc : ∀ a' b', c a' b' ≠ 0 → a' < b')
    (h : Pi.single b (1 : ℝ) - Pi.single a 1 = ∑ a', ∑ b', (c a' b' : ℝ) • root a' b') : False := by
  apply CompanionTheory.RgFd.CkM.not_cone_neg_root <;> assumption

theorem uEv_hw {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    dTau ε m (single a b 1) (uEv ε m) = 0 := by
  apply CompanionTheory.RgFd.CkM.uEv_hw <;> assumption

theorem evaluation_longest_weyl_one {ε : Fin n → Bool} {m : Fin n → ℤ} : ev ε m (w0 ε m) = 1 := by
  rw [ev_apply]; exact highest_weight_fn_K_one ε m

theorem uEv_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    uEv ε m = ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) • wN ε m := by
  exact _root_.CompanionTheory.RgFd.CkM.uEv_eq hm

theorem ckModel : PositivityTheory.RgFd.CkModel := by
  intro n ε m hm k
  unfold PositivityTheory.RgFd.cK
  rw [model_op, model_w]
  show ‖⟪wN ε m, tauC ε m k (wN ε m)⟫_ℂ‖ = _
  have hw0 : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.2 (highest_weight_vector_ne_zero ε m)
  have h1 : ⟪wN ε m, tauC ε m k (wN ε m)⟫_ℂ = ((‖w0 ε m‖ : ℝ) : ℂ) * ⟪uEv ε m, tauC ε m k (wN ε m)⟫_ℂ := by
    rw [uEv_eq hm, inner_smul_left, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw0]
    simp
  rw [h1, inner_uEv, ev_apply, tauC_fn]
  show ‖((‖w0 ε m‖ : ℝ) : ℂ) * (wN ε m).fn (1 * k)‖ = _
  rw [one_mul, wN, MV.fn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw0]
  simp [w0, MV.fn, MV.mk]

end PositivityTheory.RgFd.CkM
