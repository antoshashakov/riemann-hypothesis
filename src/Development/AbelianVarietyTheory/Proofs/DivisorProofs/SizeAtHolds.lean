module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FourMulQLeCondN
import Formalism.LocalRingCardinality.HostCls
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SizeProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sizes

variable {D : D7} {L : SizeData₂ D}

theorem cloudLen_le (L : SizeData₂ D) : (cloudLen D : ℝ) ≤ L.Sc := by
  have key : ∀ τ i, 0 ≤ (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i ∧
      (((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v i : ℤ) : ℝ) ≤ L.Sc := fun τ i => by
    dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v τ ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc τ).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc τ).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc τ).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  have h0 := L.Sc_pos.le
  have hL : cloudLen D ≤ ⌊L.Sc⌋₊ := by
    unfold cloudLen
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := key τ 2
    obtain ⟨b0, -⟩ := key τ D.R.k
    generalize (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 = u at *
    generalize (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k = v at *
    have h : ((u - v).toNat : ℤ) ≤ u := by omega
    have h' : (((u - v).toNat : ℤ) : ℝ) ≤ ((u : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (cloudLen D : ℝ) ≤ (⌊L.Sc⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ L.Sc := Nat.floor_le h0

theorem gap_le (D : D7) (B : ℝ) (hB : 1 ≤ B) (hc : Real.sqrt (cloudLen D) ≤ B) (hm : 44 ≤ D.R.m) :
    (gap D 1 : ℝ) ≤ 4 * (D.R.t : ℝ) ^ 7 * B := by
  have h1 := D.R.rank_add_five_le
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.m_add_three_le_k
  have hr : D.R.r + 5 ≤ D.R.t := h1
  have hk : D.R.k ≤ D.R.t := by omega
  set t := D.R.t with ht
  have hN : bigN D ≤ 5 * t ^ 2 := by
    unfold bigN sLen
    have : D.R.m * (t + (D.R.r + 6) + 1) ≤ t * (3 * t) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hn : nRk D ≤ t := by unfold nRk; omega
  have hs : sLen D ≤ 2 * t := by unfold sLen; omega
  have t1 : (132 : ℝ) ≤ t := by exact_mod_cast (by omega : 132 ≤ t)
  have hN' : (bigN D : ℝ) ≤ 5 * (t : ℝ) ^ 2 := by exact_mod_cast hN
  have hn' : (nRk D : ℝ) ≤ t := by exact_mod_cast hn
  have hs' : (sLen D : ℝ) ≤ 2 * t := by exact_mod_cast hs
  have hm' : (D.R.m : ℝ) ≤ t := by exact_mod_cast (by omega : D.R.m ≤ t)
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have a1 : (bigN D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 := by
    calc (bigN D : ℝ) ^ 3 ≤ (5 * (t : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hN' 3
      _ = 125 * (t : ℝ) ^ 6 := by ring
      _ ≤ t * (t : ℝ) ^ 6 := by gcongr; linarith
      _ = _ := by ring
  have a2 : (nRk D : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 := pow_le_pow_left₀ (by positivity) hn' 7
  have a3 : (nRk D : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 :=
    (pow_le_pow_left₀ (by positivity) hn' 3).trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have a4 : 132 * (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 7 := by
    calc 132 * (t : ℝ) ^ 3 ≤ t * (t : ℝ) ^ 3 := by gcongr
      _ = (t : ℝ) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  have a5 : (t : ℝ) ≤ (t : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have a6 : (t : ℝ) ^ 7 ≤ (t : ℝ) ^ 7 * B := le_mul_of_one_le_right (by positivity) hB
  have a7 : (nRk D : ℝ) ^ 3 * Real.sqrt (cloudLen D) ≤ (t : ℝ) ^ 7 * B := by gcongr
  have a8 : Real.sqrt D.R.m ≤ t := (Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩)
  have a9 : (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 3 := by
    calc (nRk D : ℝ) ^ 2 * Real.sqrt D.R.m ≤ (t : ℝ) ^ 2 * t := by gcongr
      _ = _ := by ring
  unfold gap
  push_cast
  refine max_le (max_le ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_) ?_) ((Nat.ceil_lt_add_one (by positivity)).le.trans ?_)
  · linarith
  · linarith
  · linarith

theorem hc_bounds (P : ParameterChoice' D L) (hS : SizesAt L) (hx : L.sc.x ≤ L.sc.X') (τ) (l : Fin D.R.m) :
    0 < (D.hc τ).b l ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b := by
  have x1 := L.sc.one_lt_alt
  have x0 : 0 < L.sc.x := by linarith
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg x0.le _)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.n_pos'
  have hb' : L.sc.b' ≤ L.sc.b := by
    unfold Scale.b' Scale.a
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hb0 : 0 < L.sc.b' := by unfold Scale.b' Scale.a; have : 0 < L.sc.X' := by linarith
                               positivity
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb0.le x1.le
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb0.le x0 (by nlinarith)
  have hw0 : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have he : L.etaSz < L.sc.w'' D.R.n := by
    have h1 := P.teta
    have h2 : L.sc.w'' D.R.n / L.sc.x < L.sc.w'' D.R.n := div_lt_self hw0 x1
    have := L.etaSz_pos
    nlinarith
  have hwj : wj D (l.1 + 1) τ = (((D.hc τ).e l : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simp)]
    rfl
  have hbT : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have h1 := P.bT_le t
    have h2 := P.rho_le
    have hLa : 0 ≤ L.LaG := (Real.rpow_nonneg x0.le _).trans hS.2.2.2.2.2.2.2.2.1.1
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos x1.le (by norm_num)
    have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
      have := P.Crho_pos; have := Real.log_nonneg x1.le; positivity
    unfold LevelStarExponents.rhoP at h2
    have h5 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      linarith
    have : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    nlinarith
  have key : L.sc.w'' D.R.n ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * L.sc.b := by
    rw [← hwj]
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      obtain ⟨t, ht1, ht2⟩ : ∃ t ∈ D.host.TT, D.R.tau1 t = (D.eTau τ : D.R.GG) := by
        unfold Host.topPlaces at h1
        simpa using h1
      have := L.win_top (l.1 + 1) (by omega) l.2 τ ⟨t, ht1⟩ ht2.symm
      have a := L.bT_ge ⟨t, ht1⟩
      have b := hbT ⟨t, ht1⟩
      constructor <;> linarith [this.1, this.2]
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have := L.win_thick (l.1 + 1) (by omega) l.2 τ h2
        constructor <;> linarith [this.1, this.2]
      · have := L.win_thin (l.1 + 1) (by omega) l.2 τ ⟨(D.eTau τ).2, h1, h2⟩
        constructor <;> linarith [this.1, this.2]
  refine ⟨?_, key.2⟩
  have := (abs_le.1 (L.be_close τ l l)).1
  push_cast at this
  have : (0 : ℝ) < (((D.hc τ).b l : ℚ) : ℝ) := by linarith [key.1]
  exact_mod_cast this

end Sizes

section Main

variable {D : D7} {L : SizeData₂ D}



theorem sizeRows_fam {eps : ℝ} (he : 0 < eps) (Fm : FamP eps) (h : FamHyp Fm) :
    ∃ x₀ : ℝ, ∀ x, Fm.x1 < x → x₀ ≤ x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows (Fm.L x i) := by
  refine ⟨max (44 ^ 4) ((8 : ℝ) ^ (4 / eps)), fun x hx h0 i => ?_⟩
  obtain ⟨⟨hn, -⟩, ⟨hm0, hm1⟩, hk, -⟩ := h.2.1 x hx i
  obtain ⟨hc, -, hg, -⟩ := h.1.2.2.2.2.2.2.2.2 x hx i
  have ex := Fm.L_x x i hx
  have ee := Fm.L_eps x i
  refine _root_.GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of (Fm.params x hx i) (Fm.parT x hx i) (Fm.fixed.2.2.2.2.2.2.2 x hx i).1 (Fm.sizes x hx i)
    (by rw [ex, ee]; exact hn) (by rw [ex]; exact hm0) (by rw [ex]; exact hm1) (by rw [ex, ee]; exact hk) hg
    (h.2.2.1 x hx i) hc ?_ (by rw [ex]; exact le_of_max_le_left h0)
  rw [ex, ee]
  have e1 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e1]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right h0) (by positivity)

end Main

end GlobalTheory.BigTop.Fun.SizeProof

end
