module

public import Formalism.PeriodIntegrals.ExplicitFormula
public import Formalism.PeriodIntegrals.ZerosWindow
import Mathlib

/-! Explicit formula for primitive Dirichlet L-functions and the count of zeros near height t.
Shorter proof: zero factorization via Mathlib's divisor/`extract_zeros_poles` and Borel–Carathéodory.
Adapted from Playground attempt #99125 (Osgood001/riemann-hypothesis, Core Pillar 3). -/


noncomputable section

open Complex hiding log log_inv norm_natCast exp_nat_mul cosh log_mul
open Real hiding Gamma sin_add_pi_div_two norm_natCast
open Finset hiding uIcc Icc uIcc_of_le
open Set hiding mem_Icc mem_range
open MeasureTheory hiding integral_smul integral_const_mul integral_div norm_integral_le_of_norm_le_const integral_neg
open Filter hiding mem_sdiff
open Topology Metric DirichletCharacter intervalIntegral Or LSeries Asymptotics IsBigO
open ArithmeticFunction hiding log
open Nat (cast_analyticOrderNatAt lt_floor_add_one succ_pos one_le_iff_ne_zero floor_le cast_sub cast_pos cast_nonneg one_le_cast strong_induction_on exists_eq_succ_of_ne_zero add_sub_of_le cast_eq_zero cast_add_one cast_ofNat cast_sum cast_zero cast_lt cast_le lt_of_floor_lt floor measurable_floor floor_eq_iff)
open Int (fract abs_fract fract_lt_one natCast_floor_eq_floor natCast_ne_zero)
open Iff (mp mpr)
open Eventually (of_forall mono)
open Set.Finite (toFinset mem_toFinset toFinset_mono toFinset_subset)
open MeromorphicOn (divisor)
open LE.le (trans_eq)
open Inv (inv)
open Function (mem_support)
open NeZero (pos ne)
open Classical

namespace EF

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

abbrev cext := @Complex.ext
abbrev τ : ℂ := 2 * π
abbrev τI : ℂ := τ * I
abbrev rN (n : ℕ) : ℝ := n
abbrev cR (x : ℝ) : ℂ := x
abbrev cpx := Complex.mk
abbrev aim (z : ℂ) := abs (im z)
abbrev LN (N : ℕ) (t : ℝ) : ℝ := log (N * (abs t + 2))
abbrev ldL := logDeriv (LFunction χ)
lemma one_le_N (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := mpr one_le_cast (pos N)
lemma half_le_log {x} (h : 2 ≤ x := by nlinarith) : 0.69 ≤ log x := by linarith [log_le_log two_pos h, log_two_gt_d9]
lemma half_le_LN (N : ℕ) [NeZero N] t : 0.69 ≤ LN N t := half_le_log (by nlinarith [one_le_N N,
                                                                                    abs_nonneg t])
lemma log_le_2log {x y} (h : x ≤ y ^ 2) (hx : 0 < x := by positivity) : log x ≤ 2 * log y := by
  simpa using trans_eq (log_le_log hx h) $ log_pow y 2
lemma arsinh_le_log {x} (hx : 0 ≤ x := by linarith) : arsinh x ≤ log (1 + 2 * x) := by
  apply log_le_log
  positivity
  nlinarith [sq_sqrt $ show 0 ≤ 1 + x ^ 2 by positivity, sqrt_nonneg $ 1 + x ^ 2]
lemma nneg {a : ℂ} {B} (h : norm a ≤ B) : norm (-a) ≤ B := by simpa using h
lemma nadd3 {a b c d : ℂ} {B C D} (hb : norm b ≤ B) (hc : norm c ≤ C) (hd : norm d ≤ D) (h : a = b + c + d := by ring1) :
    norm a ≤ B + C + D := by
  subst h
  grw [norm_add₃_le, hb, hc, hd]

def ZerosBelow T :=
  {ρ | 0 < re ρ ∧ re ρ < 1 ∧ |im ρ| < T ∧ LFunction χ ρ = 0}

def ZerosNear t :=
  {ρ | 0 < re ρ ∧ re ρ < 1 ∧ |im ρ - t| ≤ 1 ∧ LFunction χ ρ = 0}

abbrev mult ρ := analyticOrderNatAt (LFunction χ) ρ
abbrev mC (ρ : ℂ) : ℂ := mult χ ρ
abbrev mR ρ := rN (mult χ ρ)

def del1 : ℂ := if χ = 1 then 1 else 0

def psiRaw (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)

def zsum T (u : ℝ) := ∑ᶠ ρ ∈ ZerosBelow χ T, mC χ ρ * (↑u ^ ρ / ρ)
def S1 := ∑ᶠ ρ ∈ ZerosBelow χ 1, mR χ ρ / norm ρ

def GoodHeight T' :=
  ∀ ρ, 0 < re ρ → re ρ < 1 → LFunction χ ρ = 0 →
    inv (1600 * log (N * T')) ≤ |(|im ρ|) - T'|

def cLine u := 1 + inv (log u)

lemma rpow_cLine_ef {u} (hu : 2 ≤ u := by linarith) : u ^ cLine u = rexp 1 * u := by
  rw [cLine, rpow_add, rpow_one, rpow_def_of_pos, mul_inv_cancel₀ (log_pos _).ne',
      mul_comm] <;> linarith

def Err (N : ℕ) u T := u * log (N * u * T) ^ 2 / T + log (N * u)

def rectInt (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :=
  (∫ x in x0..x1, f (cpx x y0)) - (∫ x in x0..x1, f (cpx x y1)) +
    I • (∫ y in y0..y1, f (cpx x1 y)) - I • ∫ y in y0..y1, f (cpx x0 y)

def rect (x0 x1 y0 y1 : ℝ) := Icc x0 x1 ×ℂ Icc y0 y1

def perronK (y : ℝ) c T :=
  inv τ * ∫ t in (-T)..T, ↑y ^ cpx c t / cpx c t

def kb T y := if log y = 0 then 1 + arsinh T else min (1 + arsinh T) (inv (T * abs (log y)))

lemma norm_int_inv_sqrt {f : ℝ → ℂ} {T : ℝ} {C} (hT : 0 ≤ T) (h : ∀ t ∈ Ioc (-T) T,
                                                              ‖f t‖ ≤ C * inv √(1 + t ^ 2)) :
    ‖∫ t in -T..T, f t‖ ≤ 2 * C * arsinh T := by
  have hci : IntervalIntegrable (fun t => inv √(1 + t ^ 2)) volume (-T) T :=
    Continuous.intervalIntegrable (by fun_prop (disch := intro _
                                                         positivity)) _ _
  grw [norm_integral_le_of_norm_le _ (of_forall h) $ hci.const_mul C]
  rw [integral_const_mul, integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_arsinh t) hci,
      arsinh_neg]
  linarith
  linarith

def vertInt u T' :=
  inv τ * ∫ t in (-T')..T',
    let z := cpx (cLine u) t
    (-ldL χ z) * (↑u ^ z / z)

variable {χ : DirichletCharacter ℂ N}
lemma ne_one_of_ne_one (h : χ ≠ 1) : N ≠ 1 := fun hN => h (by subst hN
                                                              exact level_one χ)
lemma norm_del1 : ‖del1 χ‖ ≤ 1 := by
  unfold del1
  split_ifs <;> simp
section InputsSec
open scoped ArithmeticFunction.Moebius

lemma logDeriv_prod_factor {f h : ℂ → ℂ} {Z} {m : ℂ → ℕ} {s}
    (hfac : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hne : ∀ ρ ∈ Z, s - ρ ≠ 0) (hh0 : h s ≠ 0) (hhd : DifferentiableAt ℂ h s) :
    logDeriv f s = logDeriv h s + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) := by
  have hp0 ρ (h : ρ ∈ Z) := pow_ne_zero (m ρ) $ hne ρ h
  rw [(logDeriv_congr_nhds hfac).eq_of_nhds]
  change logDeriv ((fun z => ∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h) s = _
  rw [logDeriv_mul s (mpr prod_ne_zero_iff hp0) hh0 _ hhd,
    ← prod_fn, logDeriv_prod hp0,
    sum_congr rfl fun _ _ => by
      rw [logDeriv_fun_pow, logDeriv_apply, deriv_sub_const, deriv_id'', mul_one_div]
      fun_prop, add_comm]
  all_goals fun_prop

open ZetaAsymptotics in
lemma tsum_rpow_le {s : ℝ} (hs : 1 < s) : ∑' n : ℕ, rN n ^ (-s) ≤ 1 + inv (s - 1) := by
  rw [(mpr summable_nat_rpow $ by linarith).tsum_eq_zero_add]
  have := zeta_limit_aux1 hs
  simp_rw [cast_zero, zero_rpow $ show -s ≠ 0 by linarith, zero_add, rpow_neg $ cast_nonneg _,
           cast_add_one, inv_eq_one_div]
  nlinarith [show 0 ≤ termTSum s from tsum_nonneg fun _ => term_nonneg _ _]

lemma mellin_strip {f : ℂ → ℂ} {g : ℝ → ℂ} {C} (hC : 0 ≤ C) (hf : Differentiable ℂ f)
    (hgm : Measurable g) (hgb : ∀ x, ‖g x‖ ≤ C)
    (heq : ∀ {z}, 1 < re z → f z = z * ∫ x in Ioi 1, g x * (x : ℂ) ^ (-z - 1))
    {s} (hs : 0.5 ≤ re s) : ‖f s‖ ≤ 2 * C * norm s := by
  let F := indicator (Ioi 1) g
  have hme z : mellin F (-z) = ∫ x in Ioi 1, g x * x ^ (-z - 1) := by
    rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi]
    simpa [Ioi_inter_Ioi] using setIntegral_congr_fun measurableSet_Ioi fun x _ => by simp [mul_comm]
  rw [show f s = s * mellin F (-s) by
    apply (hf.differentiableOn.analyticOnNhd $ isOpen_re_gt 0).eqOn_of_preconnected_of_eventuallyEq _
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by norm_num)
      (mono ((isOpen_re_gt 1).mem_nhds $ by norm_num) fun z hz => by simp [heq hz, hme]) (by
        dsimp
        linarith)
    apply DifferentiableOn.analyticOnNhd _ $ isOpen_re_gt 0
    intro z hz
    suffices DifferentiableAt ℂ (mellin F) (-z) by fun_prop
    apply mellin_differentiableAt_of_isBigO_rpow (a := 0)
    apply (locallyIntegrableOn_const C).mono (hgm.indicator measurableSet_Ioi).aestronglyMeasurable
    filter_upwards
    rotate_left
    apply of_bound C
    filter_upwards
    rotate_left
    simpa
    apply of_bound 0
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one]
    grind [indicator_of_notMem, norm_zero]
    swap
    apply sub_one_lt
    all_goals intro x
    all_goals simp [abs_of_nonneg hC]
    all_goals grw [norm_indicator_le_norm_self]
    all_goals exact hgb x]
  rw [hme, norm_mul]
  grw [MeasureTheory.norm_integral_le_of_norm_le $ (integrableOn_Ioi_rpow_of_lt (by linarith : -re s - 1 < -1) zero_lt_one).const_mul C,
    MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt _ zero_lt_one]
  simp
  grw [inv_anti₀ _ hs] <;> linarith
  linarith
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  grw [norm_mul, hgb x, norm_cpow_eq_rpow_re_of_pos $ lt_trans zero_lt_one hx]
  simp

lemma chk_lBoundRight_ef (hpx : χ ≠ 1) {s} (hs : 0.5 ≤ re s := by
                                                               simp
                                                               linarith) (h2 : re s ≤ 8 := by
                                                                                              simp
                                                                                              linarith) :
    ‖LFunction χ s‖ ≤ 20 * (N * (aim s + 2)) := by
  let Ap n := ∑ k ∈ range n, χ k
  have hzero : ∑ n ∈ range N, χ n = 0 := by
    obtain ⟨m, rfl⟩ := exists_eq_succ_of_ne_zero $ ne N
    rw [← Fin.sum_univ_eq_sum_range, ← MulChar.sum_eq_zero_of_ne_one hpx]
    exact sum_congr rfl fun (i : ZMod $ m + 1) _ => congrArg χ $ ZMod.natCast_zmod_val i
  have hB K : ‖Ap K‖ ≤ N := by
    induction K using strong_induction_on with | _ K ih =>
      by_cases hK : K < N
      grw [norm_sum_le, sum_le_sum fun _ _ => norm_le_one χ _]
      simpa using hK.le
      convert ih (K - N) (by grind [pos N]) using 2
      rw [← add_sub_of_le $ mp not_lt hK]
      simp [Ap, sum_range_add, hzero]
  have := mellin_strip (g := (fun n : ℕ => ∑ k ∈ Icc 1 n, χ k) ∘ floor) (cast_nonneg N)
    (differentiable_LFunction hpx) (measurable_from_top.comp measurable_floor)
    (fun x => by
      convert hB (⌊x⌋₊ + 1) using 2
      simp [Ap, sum_range_eq_add_Ico _ $ succ_pos _, χ.map_zero' $ ne_one_of_ne_one hpx]
      rfl)
    (fun {z} hz => by
      rw [LFunction_eq_LSeries χ hz, LSeries_eq_mul_integral' (fun n => χ n) zero_le_one hz]
      simp [sub_eq_add_neg, add_comm]
      apply isBigO_of_le
      intro n
      grw [norm_of_nonneg $ by positivity, sum_le_sum fun _ _ => norm_le_one χ _]
      simp) hs
  have := norm_le_abs_re_add_abs_im s
  have : norm s ≤ 8 + aim s := by grind
  nlinarith [one_le_N N, abs_nonneg $ im s]
end InputsSec

variable (χ)
def Lent_ef : ℂ → ℂ := if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

lemma differentiable_Lent_ef : Differentiable ℂ (Lent_ef χ) := by
  unfold Lent_ef
  split_ifs with h
  exacts [differentiable_LFunctionTrivChar₁ N, differentiable_LFunction h]

lemma analytic_Lent {U} : AnalyticOnNhd ℂ (Lent_ef χ) U :=
  fun z _ => (differentiable_Lent_ef χ).analyticAt z

lemma Lent_one_ne_zero_ef : Lent_ef χ 1 ≠ 0 := by
  unfold Lent_ef
  split_ifs with h
  exacts [LFunctionTrivChar₁_apply_one_ne_zero N, LFunction_apply_one_ne_zero h]

lemma Lent_order_ne_top (ρ) : analyticOrderAt (Lent_ef χ) ρ ≠ ⊤ := fun h =>
  Lent_one_ne_zero_ef χ $ (analytic_Lent χ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ ρ) (mp analyticOrderAt_eq_top h) $ mem_univ 1

variable {χ}
lemma Lent_one_apply_ef (h : χ = 1) {s} (hs : s ≠ 1) :
    Lent_ef χ s = (s - 1) * LFunction χ s := by
      subst h
      simp [Lent_ef, hs]

lemma Lent_eq_zero_iff_ef {s} (hs : s ≠ 1) : Lent_ef χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  simp [Lent_one_apply_ef h hs, sub_eq_zero, hs]
  simp [Lent_ef, h]

lemma order_Lent_ef {s} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent_ef χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  have h1 : AnalyticAt ℂ (· - 1) s := by fun_prop
  have hn := isOpen_ne.mem_nhds hs
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr $ mono hn fun _ => Lent_one_apply_ef h, ← Pi.mul_def,
      analyticOrderAt_mul h1 $ DifferentiableOn.analyticAt (fun z hz => (differentiableAt_LFunction χ z $ inl hz).differentiableWithinAt) hn, mpr h1.analyticOrderAt_eq_zero $ sub_ne_zero_of_ne hs, zero_add]
  simp [Lent_ef, h]

lemma mC0_zero (h : Lent_ef χ 0 ≠ 0) : mC χ 0 = 0 := by
  rw [mC, mult, ← order_Lent_ef zero_ne_one, analyticOrderNatAt,
      mpr ((differentiable_Lent_ef χ).analyticAt 0).analyticOrderAt_eq_zero h]
  simp

lemma logDeriv_Lent_ef {s} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    ldL χ s = logDeriv (Lent_ef χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  rw [(logDeriv_congr_nhds $ mono (isOpen_ne.mem_nhds hs) fun _ => Lent_one_apply_ef h).eq_of_nhds,
      ← Pi.mul_def,
    logDeriv_mul (f := (· - 1)) s (sub_ne_zero_of_ne hs) h0 _ $ differentiableAt_LFunction χ s $ inl hs,
    show logDeriv (· - 1) s = inv (s - 1) by simp [logDeriv_apply]]
  simp only [del1, ite_eq_left h]
  ring
  fun_prop
  simp [Lent_ef, del1, h]

lemma div_Lent {U u} (hu : u ∈ U) :
    divisor (Lent_ef χ) U u = analyticOrderNatAt (Lent_ef χ) u := by
  rw [MeromorphicOn.divisor_apply (analytic_Lent χ).meromorphicOn hu,
      (analytic_Lent χ u hu).meromorphicOrderAt_eq, ← cast_analyticOrderNatAt $ Lent_order_ne_top χ u]
  simp

lemma div_Lent_ne_zero {U u} (hu : u ∈ U) : divisor (Lent_ef χ) U u ≠ 0 ↔ Lent_ef χ u = 0 := by
  rw [div_Lent hu, natCast_ne_zero, ne_eq, ← cast_eq_zero (R := ℕ∞),
      cast_analyticOrderNatAt $ Lent_order_ne_top χ u,
    ((differentiable_Lent_ef χ).analyticAt u).analyticOrderAt_eq_zero, not_not]

variable (χ)
lemma extract_zeros_Lent {U} (hUc : IsCompact U) (hUp : IsPreconnected U) (hUn : U.Nontrivial) :
    ∃ Z : Finset ℂ, ∃ g, (∀ ρ, ρ ∈ Z ↔ ρ ∈ U ∧ Lent_ef χ ρ = 0) ∧
      AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧
      ∀ z ∈ U, Lent_ef χ =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ mult χ ρ) * g w := by
  have hf := analytic_Lent χ (U := U)
  let D := divisor (Lent_ef χ) U
  have hDfin := D.finiteSupport hUc
  have hmem ρ : ρ ∈ toFinset hDfin ↔ ρ ∈ U ∧ Lent_ef χ ρ = 0 := by
    by_cases h : ρ ∈ U <;> simp [h, D, div_Lent_ne_zero]
  obtain ⟨g, hg, hg0, heq⟩ := hf.meromorphicOn.extract_zeros_poles (fun ⟨u, hu⟩ => by
    simp [(hf u hu).meromorphicOrderAt_eq, Lent_order_ne_top χ u]) hDfin
  refine ⟨toFinset hDfin, g, hmem, hg, fun z hz => hg0 ⟨z, hz⟩, fun z hz => ?_⟩
  let rhs w := (∏ ρ ∈ toFinset hDfin, (w - ρ) ^ mult χ ρ) * g w
  have hrhs : AnalyticAt ℂ rhs z := (analyticAt_fun_prod _ fun _ _ => by fun_prop).mul $ hg z hz
  apply mp $ (hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hrhs.continuousAt
  apply (hf z hz).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect hrhs.meromorphicAt hz $ hUp.preperfect_of_nontrivial hUn
  apply heq.trans
  apply of_forall
  intro w
  rw [Pi.smul_apply', Function.factorizedRational,
      finprod_eq_prod_of_mulSupport_subset _ (s := hDfin.toFinset), smul_eq_mul]
  simp only [Finset.prod_apply, Pi.pow_apply]
  congr 1
  apply prod_congr rfl
  intro ρ hrx
  obtain ⟨hU, h0⟩ := mp (hmem ρ) hrx
  simp [div_Lent hU, order_Lent_ef fun e => Lent_one_ne_zero_ef χ $ e ▸ h0]
  simp [D, Function.FactorizedRational.mulSupport]

lemma zerosFinite_ef (T) : (ZerosBelow χ T).Finite :=
  ((divisor (Lent_ef χ) $ rect 0 1 (-T) T).finiteSupport $ isCompact_Icc.reProdIm isCompact_Icc).subset fun ρ ⟨h0, h1, him, hL⟩ =>
    mpr mem_support $ mpr (div_Lent_ne_zero ⟨⟨h0.le, h1.le⟩,
                                             mp abs_le him.le⟩) $ mpr (Lent_eq_zero_iff_ef $ by grind [one_re]) hL
variable {χ}

section PrimSec
variable (hpx : IsPrimitive χ)
include hpx

lemma zeroLocus_ef {s}
    (hs : -1.5 ≤ re s) (hs1 : s ≠ 1) (hL : LFunction χ s = 0) :
    (0 < re s ∧ re s < 1) ∨ s = 0 ∨ s = -1 := by
  by_cases hre0 : 0 < re s
  exact inl ⟨hre0, lt_of_not_ge fun h => LFunction_ne_zero_of_one_le_re χ (inr hs1) h hL⟩
  right
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by
    by_contra h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl : N = 1 := by simpa [IsPrimitive, conductor_one] using hpx.symm
    norm_num [LFunction_modOne_eq, riemannZeta_zero] at hL
  have hdiv := LFunction_eq_completed_div_gammaFactor χ s $ hc'.elim (inr ∘ ne_one_of_ne_one) inl
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  have := hdiv.resolve_left fun h0 => LFunction_ne_zero_of_one_le_re (inv χ) (s := 1 - s)
    (hc'.imp (mpr inv_ne_one) $ by grind) (by
      simp
      linarith) $ by
      rw [LFunction_eq_completed_div_gammaFactor (inv χ) (1 - s) $ inl $ by grind [sub_re]]
      simp [h0, (show IsPrimitive (inv χ) by rwa [IsPrimitive,
                                                  conductor_inv]).completedLFunction_one_sub s]
  have hgn {w} (hw : -1.5 ≤ re w) (h : Gammaℝ w = 0) : w = 0 := by
    obtain ⟨_ | n, rfl⟩ := mp Gammaℝ_eq_zero_iff h <;> simp at *
    linarith
  rcases even_or_odd χ with he | ho
  left
  apply hgn hs
  rwa [← he.gammaFactor_def]
  right
  apply eq_neg_of_add_eq_zero_left
  apply hgn $ by
                 simp
                 linarith
  rwa [← ho.gammaFactor_def]

lemma zeroStrip {s} (hs : -0.5 ≤ re s := by linarith) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hL : LFunction χ s = 0) :
    0 < re s ∧ re s < 1 := by
  rcases zeroLocus_ef hpx (by linarith) hs1 hL with h | rfl | rfl
  exacts [h, absurd rfl hs0, by norm_num at hs]

open scoped ZMod in
lemma norm_L_one_sub_le_ef {w}
    (h1 : 0.5 ≤ re w := by
                           simp
                           linarith) (h2 : re w ≤ 5 := by
                                                          simp
                                                          linarith) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 12 * N ^ 5 * (aim w + 7) ^ 7 * ‖LFunction (inv χ) w‖ := by
  have : ‖Gamma w‖ * rexp (π / 2 * aim w) ≤ 6 * (aim w + 7) ^ 7 := by
    let z := cpx 0.5 $ im w
    let b  := 7.5 - re w
    have hb : 2 ≤ b := by grind
    have : 1 ≤ Real.Gamma b := by simpa using Gamma_strictMonoOn_Ici.monotoneOn (a := 2) self_mem_Ici hb hb
    have hB := congrArg norm $ Gamma_mul_Gamma_eq_betaIntegral (s := w) (t := b) (by linarith) $ by
      simp
      linarith
    rw [norm_mul, norm_mul, show w + b = z + 7 from cext (by simp
                                                             ring) rfl,
      Gamma_ofReal, norm_real, norm_of_nonneg $ by linarith] at hB
    have : ‖betaIntegral w b‖ ≤ 2 := by
      grw [betaIntegral,
           norm_integral_le_of_norm_le zero_le_one _ $ intervalIntegrable_rpow' (r := -0.5) $ by norm_num,
        integral_rpow $ inl $ by norm_num]
      norm_num
      apply of_forall
      rintro x ⟨hx0, hx1⟩
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, ← ofReal_one, ← ofReal_sub,
          norm_cpow_eq_rpow_re_of_nonneg]
      grw [rpow_le_one (x := 1 - x), mul_one]
      apply rpow_le_rpow_of_exponent_ge hx0 hx1
      all_goals simp
      all_goals linarith
    have hG7z (k : ℕ) (hk : k ≤ 7) : ‖Gamma (z + k)‖ ≤ (aim w + 7) ^ k * ‖Gamma z‖ := by
      induction k with
      | zero => simp
      | succ m ih =>
        rw [cast_add_one, ← add_assoc, Complex.Gamma_add_one, norm_mul, pow_succ', mul_assoc]
        grw [norm_add_le, norm_natCast, norm_le_abs_re_add_abs_im z, ih $ by omega]
        gcongr ?_ * _
        have : rN m ≤ 6 := by
          norm_cast
          omega
        simp [z]
        linarith
        apply ne_of_apply_ne re
        simp [z]
        linarith
    have : ‖Gamma z‖ * rexp (π / 2 * aim w) ≤ 3 := by
      have h := Gamma_mul_Gamma_one_sub z
      rw [show 1 - z = (starRingEnd ℂ) z by apply cext <;> simp
                                            norm_num, Gamma_conj, mul_conj,
        show π * z = ↑(π * im w) * I + π / 2 by
          apply cext <;> simp [z]
          ring,
        sin_add_pi_div_two, cos_mul_I, ← ofReal_cosh] at h
      have : (‖Gamma z‖ * rexp (π / 2 * aim w)) ^ 2 ≤ 9 := by
        rw [mul_pow,
            (by exact_mod_cast normSq_eq_norm_sq _ ▸ h : ‖Gamma z‖ ^ 2 = π / cosh (π * im w)), ← exp_nat_mul, cast_ofNat, ← mul_assoc, mul_div_cancel₀ _ two_ne_zero,
          div_mul_eq_mul_div, div_le_iff₀ $ cosh_pos _, ← cosh_abs, abs_mul, abs_of_pos pi_pos, cosh_eq]
        nlinarith [pi_lt_four, exp_pos $ π * aim w, exp_pos $ -(π * aim w)]
      nlinarith
    have h7 := hG7z 7 le_rfl
    norm_num at h7
    grw [show ‖Gamma w‖ ≤ 2 * ‖Gamma (z + 7)‖ by nlinarith [norm_nonneg $ Gamma w,
                                                            norm_nonneg $ Gamma $ z + 7], h7]
    nlinarith [show 0 ≤ (aim w + 7) ^ 7 by positivity]
  let cf  := χ
  set L := ‖LFunction (inv χ) w‖
  let zL := @ZMod.LFunction N _
  rw [LFunction, ZMod.LFunction_one_sub _ (fun n hn => by simp [hn] at h1
                                                          linarith) h]
  have hsmul c f : zL (c • f) w = c * zL f w := by simp [zL, ZMod.LFunction, mul_sum, mul_assoc,
                                                         mul_left_comm]
  have hA : ‖zL (𝓕 cf) w‖ ≤ N * L := by
    rw [show 𝓕 cf = (gaussSum χ ZMod.stdAddChar * inv χ (-1)) • (inv χ : DirichletCharacter ℂ N) from funext fun k => by
      rw [hpx.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]
      simp
      ring, hsmul, norm_mul, norm_mul]
    unfold gaussSum
    grw [norm_sum_le, sum_le_sum fun a _ => by
      simpa [ZMod.stdAddChar_apply] using norm_le_one χ a, norm_le_one (inv χ) _]
    simp [L, zL, LFunction]
  have he {a} (ha : re a ≤ π / 2 * aim w) := (norm_exp a).symm ▸ mpr exp_le_exp ha
  simp
  rw [norm_natCast_cpow_of_pos $ pos N, ← ofReal_ofNat, ← ofReal_mul, norm_cpow_eq_rpow_re_of_pos]
  grw [rpow_le_rpow_of_exponent_le (one_le_N N) (z := (4 : ℕ)), rpow_natCast,
    rpow_le_one_of_one_le_of_nonpos,
    norm_add_le, norm_mul, norm_mul,
    he, he, hA,
    show ‖zL (𝓕 fun x => cf $ -x) w‖ ≤ N * L by
      rw [show (fun x => cf $ -x) = χ (-1) • cf from funext fun x => by simp [cf, ← map_mul],
          map_smul, hsmul, norm_mul]
      grw [norm_le_one χ $ -1, hA, one_mul]]
  nlinarith [show 0 ≤ N ^ 5 * L by positivity]
  all_goals try positivity
  all_goals try simp
  all_goals nlinarith [le_abs_self $ im w, neg_le_abs $ im w, pi_pos, pi_gt_three]

lemma lGrowth {s} (h1 : -4 ≤ re s) (h2 : re s ≤ 8) :
    ‖Lent_ef χ s‖ ≤ 34359738368 * (N * (aim s + 2)) ^ 10 := by
  set Y := aim s + 2
  have hY : 2 ≤ Y := by grind
  by_cases hc : χ = 1
  subst hc
  obtain rfl : N = 1 := by simpa [IsPrimitive, conductor_one] using hpx.symm
  simp
  rw [show Lent_ef 1 s = riemannZeta₁ s by
    by_cases hz : s = 1
    simp [Lent_ef, hz]
    simp [Lent_ef, LFunctionTrivChar₁, LFunction_modOne_eq]
    grind [riemannZeta_eq_inv_sub_mul]]
  have hzR {z} (a : 0.5 ≤ re z := by
                                     simp
                                     linarith) (b : re z ≤ 8 := by
                                                                   simp
                                                                   linarith) : ‖riemannZeta₁ z‖ ≤ 150 * (aim z + 2) ^ 2 := by
    have hfb (x : ℝ) : ‖cR $ fract x‖ ≤ 1 := by simp [abs_fract, (fract_lt_one x).le]
    have h0 := mellin_strip zero_le_one
      ((differentiable_const 1).sub differentiable_riemannZeta₀) (by fun_prop) hfb (fun {w} hw => by
        have h := LSeries_one_eq_riemannZeta hw ▸ LSeries_eq_mul_integral' 1 zero_le_one hw $ by
          simp
          rfl
        rw [setIntegral_congr_fun measurableSet_Ioi, MeasureTheory.integral_sub] at h
        rotate_left
        apply integrableOn_Ioi_cpow_of_lt (a := -w)
        simpa
        norm_num
        apply Integrable.mul_bdd
        apply integrableOn_Ioi_cpow_of_lt (a := -w - 1)
        simp
        linarith
        norm_num
        swap
        exact of_forall hfb
        fun_prop
        intro x hx
        have hx0 := lt_trans zero_lt_one hx.out
        simp [fract, ← natCast_floor_eq_floor hx0.le, neg_add_eq_sub, cpow_sub, ne_of_gt hx0]
        grind [ofReal_eq_zero]
        rw [integral_Ioi_cpow_of_lt] at h
        simp [riemannZeta₀] at h ⊢
        grind [one_re]
        simpa
        norm_num) a
    simp at h0
    rw [riemannZeta₁, ← sub_sub_cancel 1 $ riemannZeta₀ z]
    grw [norm_add_le, norm_mul, norm_sub_le, norm_sub_le, norm_one, h0]
    have : norm z ≤ 8 + aim z := by
      grw [norm_le_abs_re_add_abs_im]
      grind
    nlinarith [norm_nonneg z, abs_nonneg $ im z]
  by_cases hr : 0.5 ≤ re s
  grw [hzR hr h2, pow_le_pow_right₀]
  gcongr
  norm_num
  linarith [hY]
  norm_num
  have hge {z} (c : 0.5 ≤ norm z) (a : -4 ≤ re z := by linarith) (b : re z ≤ 0.5 := by linarith) : ‖riemannZeta₁ z‖ ≤ 2147483648 * (aim z + 2) ^ 10 := by
    have hw : 1 - z ≠ 1 := fun h => by
      simp_all
      linarith
    have hz1 := norm_L_one_sub_le_ef isPrimitive_one_level_one (w := 1 - z) (h := inr hw)
    simp [aim] at hz1
    have hne : z ≠ 1 := by grind [one_re]
    rw [show riemannZeta₁ z = (z - 1) * riemannZeta z by grind [riemannZeta_eq_inv_sub_mul hne],
        norm_mul, norm_sub_rev]
    grw [hz1]
    rw [riemannZeta_eq_inv_sub_mul hw, sub_sub_cancel_left, norm_mul, norm_inv, norm_neg]
    grw [inv_anti₀ _ c, hzR (z := 1 - z), norm_le_abs_re_add_abs_im $ 1 - z,
      show aim z + 7 ≤ 4 * (aim z + 2) by linarith [abs_nonneg $ im z]]
    simp [aim]
    grw [show |1 - re z| + |im z| ≤ 3 * (|im z| + 2) by grind]
    ring_nf
    gcongr <;> norm_num
    norm_num
  by_cases hn : 0.5 ≤ norm s
  grw [hge hn]
  gcongr
  norm_num
  grw [norm_le_of_forall_mem_frontier_norm_le (C := 2147483648 * (2.5) ^ 10) isBounded_ball differentiable_riemannZeta₁.differentiableOn.diffContOnCl _
      (subset_closure $ mpr mem_ball_zero_iff $ mp not_le hn),
    ← hY]
  norm_num
  intro z hz
  rw [frontier_ball 0 $ by norm_num, mem_sphere_zero_iff_norm] at hz
  have ⟨hr1, hr2⟩ := mp abs_le $ hz ▸ abs_re_le_norm z
  grw [hge hz.ge]
  gcongr
  linarith [abs_im_le_norm z]
  simp [Lent_ef, hc]
  have := one_le_N N
  by_cases hr : 0.5 ≤ re s
  nlinarith [chk_lBoundRight_ef hc hr h2,
             le_self_pow₀ (by nlinarith : 1 ≤ N * Y) (by norm_num : 10 ≠ 0)]
  have hL1 := norm_L_one_sub_le_ef hpx (w := 1 - s) (h := inl $ χ.map_zero' $ ne_one_of_ne_one hc)
  rw [sub_sub_cancel] at hL1
  simp [aim] at hL1
  have hL2 := chk_lBoundRight_ef (mpr inv_ne_one hc) (s := 1 - s)
  simp [aim] at hL2
  grw [hL1, hL2, show aim s + 7 ≤ 4 * Y by linarith]
  have : N ^ 6 * Y ^ 8 ≤ (N * Y) ^ 10 := by
    rw [mul_pow]
    gcongr <;> nlinarith
  nlinarith [show 0 ≤ (N * Y) ^ 10 by positivity]

lemma Lent_local t :
    let c := cpx 2 t
    ∃ Z : Finset ℂ, (∀ ρ, ρ ∈ Z ↔ ρ ∈ closedBall c 3 ∧ Lent_ef χ ρ = 0) ∧
      ZerosNear χ t ⊆ (Z : Set ℂ) ∧
      (∑ ρ ∈ Z, mR χ ρ) ≤ 132 * LN N t ∧
      ∀ s ∈ closedBall c 2.5, Lent_ef χ s ≠ 0 →
        ‖logDeriv (Lent_ef χ) s - ∑ ρ ∈ Z, mC χ ρ / (s - ρ)‖ ≤ 5808 * LN N t := by
  intro c0
  set X := N * (abs t + 2)
  set B := 2 ^ 56 * X ^ 10
  set M := log B
  let f := Lent_ef χ
  let B6 := closedBall c0 6
  let B3 := closedBall c0 3
  let O3 := ball c0 3
  have h2arg : 2 ≤ X := by nlinarith [one_le_N N, abs_nonneg t]
  have : 1 ≤ X ^ 10 := one_le_pow₀ $ by linarith
  have : 0.5 ≤ ‖f c0‖ := by
    have hL2 : 0.5 ≤ ‖LFunction χ c0‖ := by
      have : 1 ≤ ‖LFunction χ c0‖ * 2 := by
        grw [← @norm_one ℂ, ← DirichletCharacter.LSeries.mul_mu_eq_one χ (s := c0) one_lt_two,
          ← LFunction_eq_LSeries χ one_lt_two, norm_mul, LSeries,
          tsum_of_norm_bounded (mpr (summable_nat_rpow (p := -2)) $ by norm_num).hasSum, tsum_rpow_le one_lt_two]
        norm_num
        intro n
        cases n
        simp
        rw [norm_term_eq]
        simp [c0]
        grw [norm_le_one χ _, show |(moebius _ : ℝ)| ≤ 1 by exact_mod_cast abs_moebius_le_one]
        simp
      linarith
    by_cases h : χ = 1
    dsimp [f]
    rw [Lent_one_apply_ef h $ by grind [one_re], norm_mul]
    grw [← re_le_norm $ c0 - 1, ← hL2] <;> norm_num [c0]
    simpa [f, Lent_ef, h] using hL2
  have hf0 : f c0 ≠ 0 := by grind [norm_zero]
  have hM := log_pos $ show 1 < B by nlinarith
  have : M ≤ 66 * LN N t := by
    dsimp [M, B, LN]
    rw [log_mul, log_pow, log_pow]
    push_cast
    linarith [log_le_log two_pos h2arg]
    positivity
    positivity
  have hb z (hz : z ∈ B6) : ‖f z‖ ≤ B * ‖f c0‖ := by
    rw [mem_closedBall_iff_norm] at hz
    have := abs_re_le_norm $ z - c0
    have := abs_im_le_norm $ z - c0
    simp at *
    grw [lGrowth hpx, show aim z + 2 ≤ 4 * (abs t + 2) by grind]
    rw [mul_left_comm, mul_pow]
    nlinarith
    grind
    grind
  have hsub6 := closedBall_subset_closedBall (x := c0) (by norm_num : (3 : ℝ) ≤ 6)
  obtain ⟨Zall, g, hZall, hg, hg0,
          hfac0⟩ := extract_zeros_Lent χ (isCompact_closedBall c0 6) (convex_closedBall c0 6).isPreconnected ⟨c0, mem_closedBall_self $ by norm_num, c0 + 6, by simp, by simp⟩
  set Z := Zall.filter (· ∈ B3)
  let h z := (∏ ρ ∈ Zall.filter (· ∉ B3), (z - ρ) ^ mult χ ρ) * g z
  have hZ ρ : ρ ∈ Z ↔ ρ ∈ B3 ∧ f ρ = 0 := by grind
  have hh : AnalyticOnNhd ℂ h B6 := fun z hz => (analyticAt_fun_prod _ fun _ _ => by fun_prop).mul $ hg z hz
  have hh0 {z} (hz : z ∈ B3) : h z ≠ 0 := mul_ne_zero (mpr prod_ne_zero_iff fun ρ hrx => pow_ne_zero _ $ sub_ne_zero_of_ne fun e => (mp mem_filter hrx).2 $ e ▸ hz) $ hg0 z $ hsub6 hz
  have hfac z (hz : z ∈ B6) : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ mult χ ρ) * h w :=
    (hfac0 z hz).trans $ of_forall fun w => by
      dsimp
      rw [← mul_assoc, prod_filter_mul_prod_filter_not Zall (· ∈ B3)]
  have hh_le z (hz : z ∈ B6) : ‖h z‖ ≤ B * ‖h c0‖ := by
    apply norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hh.differentiableOn.diffContOnCl_ball subset_rfl)
    rotate_left
    rwa [closure_ball c0 $ by norm_num]
    intro w hw
    rw [frontier_ball c0 $ by norm_num, mem_sphere_iff_norm] at hw
    have hw6 := mpr mem_closedBall_iff_norm hw.le
    have hρ ρ (hrx : ρ ∈ Z) := mp mem_closedBall_iff_norm (mp (hZ ρ) hrx).1
    have hlow ρ (hrx : ρ ∈ Z) : 3 ≤ ‖w - ρ‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub w ρ c0, hρ ρ hrx]
    have hbw := hb w hw6
    rw [(hfac w hw6).eq_of_nhds, (hfac c0 $ mem_closedBall_self $ by norm_num).eq_of_nhds] at hbw
    simp at hbw
    refine le_of_mul_le_mul_left (le_trans hbw ?_) $ prod_pos fun ρ hrx => pow_pos (by linarith [hlow ρ hrx]) _
    rw [mul_left_comm]
    gcongr with ρ hrx
    rw [norm_sub_rev]
    linarith [hρ ρ hrx, hlow ρ hrx]
  refine ⟨Z, hZ, fun ρ ⟨h0, h1, him, hL⟩ => mpr (hZ ρ) ⟨by
    rw [mem_closedBall_iff_norm]
    grw [norm_le_abs_re_add_abs_im]
    simp
    grind,
    mpr (Lent_eq_zero_iff_ef $ by grind [one_re]) hL⟩, ?_, fun s hs hfs => ?_⟩
  apply le_trans _ $ ((analytic_Lent χ).sum_divisor_le (c := c0) (r := 3) (R := 6) (M := B * ‖f c0‖) _ _ _ hf0 _).trans _
  rw [abs_of_pos three_pos, finsum_eq_sum_of_support_subset _ fun u hu => by
    have hu' := (divisor f _).supportWithinDomain hu
    exact mpr (hZ u) ⟨hu', mp (div_Lent_ne_zero hu') hu⟩]
  push_cast
  apply sum_le_sum
  intro u hu
  obtain ⟨hB3, hf0'⟩ := mp (hZ u) hu
  rw [div_Lent hB3, order_Lent_ef fun e => Lent_one_ne_zero_ef χ $ e ▸ hf0']
  simp
  norm_num
  norm_num
  nlinarith
  intro z hz
  exact hb z $ sphere_subset_closedBall $ by simpa using hz
  have := half_le_log (x := 6 / 3)
  rw [mul_div_cancel_right₀ _ $ mpr norm_ne_zero_iff hf0, div_le_iff₀]
  nlinarith
  linarith
  have hs3 : s ∈ O3 := closedBall_subset_ball (by norm_num) hs
  have hsR := hsub6 $ ball_subset_closedBall hs3
  rw [logDeriv_prod_factor (hfac s hsR) (fun ρ hrx h0 => hfs $ mp sub_eq_zero h0 ▸ (mp (hZ ρ) hrx).2)
    (hh0 $ ball_subset_closedBall hs3) (hh s hsR).differentiableAt, add_sub_cancel_right, logDeriv_apply]
  have hhd := hh.differentiableOn.mono $ ball_subset_closedBall.trans hsub6
  have hneB z (hz : z ∈ O3) := hh0 $ ball_subset_closedBall hz
  obtain ⟨L, hL0, hLd⟩ := ((hhd.deriv isOpen_ball).div hhd hneB).isExactOn_ball.with_val_at c0 0
  have hLd_diff : DifferentiableOn ℂ L O3 := (hLd · · |>.differentiableAt.differentiableWithinAt)
  obtain ⟨c, hc0,
          hfg⟩ := mp (logDeriv_eqOn_iff hhd hLd_diff.cexp isOpen_ball isPreconnected_ball (by simp) hneB)
    fun z hz' => by simp [logDeriv_apply, (hLd z hz').cexp.deriv]
  have hmem u (hu : u ∈ ball (0 : ℂ) 3) : c0 + u ∈ O3 := by simpa [O3, mem_ball_iff_norm] using hu
  have hsub1 : closedBall s 0.25 ⊆ closedBall c0 2.75 := closedBall_subset_closedBall' $ by linarith [mp mem_closedBall hs]
  rw [← Pi.div_apply, ← (hLd s hs3).deriv]
  grw [norm_deriv_le_of_forall_mem_sphere_norm_le (C := 22 * M) _
    (hLd_diff.diffContOnCl_ball $ hsub1.trans $ closedBall_subset_ball $ by norm_num)]
  norm_num
  linarith
  intro x hx
  have := mp mem_closedBall_iff_norm $ hsub1 $ sphere_subset_closedBall hx
  have h1 := borelCaratheodory_zero hM (hLd_diff.comp (differentiableOn_id.const_add c0) hmem) (fun u hu => by
    dsimp
    rw [le_log_iff_exp_le]
    simpa [hfg $ hmem u hu, hfg $ mem_ball_self three_pos, hL0, norm_exp, mul_comm B,
           mpr norm_pos_iff hc0] using
      hh_le (c0 + u) $ hsub6 $ ball_subset_closedBall $ hmem u hu
    positivity) three_pos (mpr mem_ball_zero_iff $ by linarith) $ by simp [hL0]
  simp at h1
  grw [h1]
  rw [div_le_iff₀] <;> nlinarith
  norm_num

lemma mC0_le t : ‖mC χ 0‖ ≤ 132 * LN N t := by
  by_cases hL : Lent_ef χ 0 = 0
  obtain ⟨Z, hZ, -, hcnt, -⟩ := Lent_local hpx 0
  grw [show ‖mC χ 0‖ ≤ 132 * LN N 0 by
      simpa [mC, mR] using le_trans (single_le_sum (fun _ _ => cast_nonneg _) $ mpr (hZ 0) ⟨by
        simp [mk_eq_add_mul_I]
        norm_num, hL⟩) hcnt]
  simp [LN]
  gcongr
  linarith [one_le_N N]
  simp
  rw [mC0_zero hL, norm_zero]
  linarith [half_le_LN N t]

lemma zerosWindow t :
    (ZerosNear χ t).Finite ∧ ∑ᶠ ρ ∈ ZerosNear χ t, mR χ ρ ≤ 132 * LN N t := by
  obtain ⟨Z, -, hsub, hcnt, -⟩ := Lent_local hpx t
  have hfin := Z.finite_toSet.subset hsub
  exists hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  grw [sum_le_sum_of_subset_of_nonneg (mpr (toFinset_subset (hs := hfin)) hsub) fun _ _ _ => cast_nonneg _, hcnt]

theorem localLemma {s}
    (hLs : LFunction χ s ≠ 0) (hs1 : s ≠ 1) (h1 : -0.5 ≤ re s := by
                                                                    simp
                                                                    linarith) (h2 : re s ≤ 3 := by
                                                                                                   simp
                                                                                                   linarith) :
    ‖ldL χ s - (∑ᶠ ρ ∈ ZerosNear χ $ im s, mC χ ρ / (s - ρ)) - mC χ 0 / s + del1 χ / (s - 1)‖ ≤
      6210 * LN N (im s) := by
  set t := im s
  set c := cpx 2 t
  have := half_le_LN N t
  obtain ⟨Z, hZ, hsub, hcnt, hbound⟩ := Lent_local hpx t
  have hb := hbound s (by
    rw [mem_closedBall_iff_norm]
    have e : s - c = ((re s - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [c, t]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith)
    fun h => hLs $ mp (Lent_eq_zero_iff_ef hs1) h
  have hZN := Z.finite_toSet.subset hsub
  set E := (Z \ toFinset hZN).erase 0
  let F ρ := mC χ ρ / (s - ρ)
  let Z0 := if 0 ∈ Z then F 0 else 0
  have hdec : ∑ ρ ∈ Z, F ρ = (∑ᶠ ρ ∈ ZerosNear χ t, F ρ) + (∑ ρ ∈ E, F ρ) + Z0 := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hZN,
        ← sum_sdiff $ mpr (toFinset_subset (hs := hZN)) hsub]
    dsimp [Z0, E]
    split_ifs with hD
    rw [← add_sum_erase _ _ $ mpr mem_sdiff ⟨hD, by simp [ZerosNear]⟩]
    ring
    simp_all
  have hfar : ‖∑ ρ ∈ E, F ρ‖ ≤ 264 * LN N t := by
    grw [norm_sum_le, sum_le_sum (g := fun ρ => 2 * mR χ ρ),
      ← mul_sum, sum_le_sum_of_subset_of_nonneg ((erase_subset _ _).trans sdiff_subset) fun _ _ _ => cast_nonneg _, hcnt]
    linarith
    intro ρ hrx
    simp [E, hZ, ZerosNear, dist_eq_norm] at hrx
    obtain ⟨hne0, ⟨hBρ, hfρ⟩, hnot⟩ := hrx
    have hne1 : ρ ≠ 1 := fun e => Lent_one_ne_zero_ef χ $ e ▸ hfρ
    have hL := mp (Lent_eq_zero_iff_ef hne1) hfρ
    have := abs_re_le_norm $ ρ - c
    simp at *
    have hd : 0.5 ≤ ‖s - ρ‖ := by
      rcases zeroLocus_ef hpx (by have h := abs_le.mp (le_trans this hBρ); have hc : c.re = 2 := rfl; rw [hc] at h; linarith [h.1]) hne1 hL with ⟨a, b⟩ | rfl | rfl
      grw [← abs_im_le_norm]
      simp
      have h3 : ¬ |ρ.im - t| ≤ 1 := fun h => hnot a b h hL
      have e : t = s.im := rfl
      rw [e, not_le] at h3
      rw [abs_sub_comm]; linarith
      exact absurd rfl hne0
      grw [← re_le_norm]
      simp
      linarith
    rw [norm_div, norm_natCast, mR, rN]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (mult χ ρ)]
  have hzero : ‖Z0 - mC χ 0 / s‖ ≤ 132 * LN N t := by
    dsimp [Z0]
    split_ifs with h0
    simp [F]
    linarith
    by_cases hL0 : Lent_ef χ 0 = 0
    have := hZ 0
    simp [h0, hL0, dist_eq_norm] at this
    grw [norm_le_abs_re_add_abs_im] at this
    simp at this
    rw [zero_sub, norm_neg, norm_div]
    grw [div_le_self $ norm_nonneg _, mC0_le hpx t]
    linarith [abs_im_le_norm s]
    simp [mC0_zero hL0]
    linarith
  grw [nadd3 hb hfar hzero (by rw [logDeriv_Lent_ef hs1 hLs, hdec]
                               ring1)]
  linarith

lemma sum_mult_le {T}
    B (hB : ∀ ρ ∈ B,
       ρ ∈ ZerosNear χ (T + 0.5) ∪ ZerosNear χ (-(T + 0.5))) (hT : 0 ≤ T := by linarith) :
    ∑ ρ ∈ B, mR χ ρ ≤ 264 * log (N * (T + 3)) := by
  obtain ⟨hf1, hw1⟩ := zerosWindow hpx $ T + 0.5
  obtain ⟨hf2, hw2⟩ := zerosWindow hpx $ -(T + 0.5)
  have h1 := le_trans (sum_le_sum_of_subset_of_nonneg (fun x hx => by simpa using hB x hx : B ⊆ toFinset hf1 ∪ toFinset hf2) fun _ _ _ => cast_nonneg _)
    (trans_eq (le_add_of_nonneg_right $ sum_nonneg fun _ _ => cast_nonneg _) $ sum_union_inter (f := mR χ))
  rw [← finsum_mem_eq_finite_toFinset_sum _ hf1, ← finsum_mem_eq_finite_toFinset_sum _ hf2] at h1
  simp only [LN, abs_neg, abs_of_nonneg $ show 0 ≤ T + 0.5 by linarith] at hw1 hw2
  have := one_le_N N
  have : log (N * (T + 0.5 + 2)) ≤ log (N * (T + 3)) := log_le_log (by nlinarith) $ by nlinarith
  linarith

lemma norm_logDeriv_le_ef {s}
    (hs0 : 0.5 ≤ norm s) (hs1 : 0.5 ≤ ‖s - 1‖)
    {K} (hK : 0 < K) (h : ∀ ρ ∈ ZerosNear χ (im s), inv K ≤ ‖s - ρ‖)
    (h1 : -0.5 ≤ re s := by linarith)
    (h2 : re s ≤ 3 := by linarith) :
    ‖ldL χ s‖ ≤ 6480 * LN N (im s) + 132 * LN N (im s) * K := by
  have hne1 : s ≠ 1 := fun h => by norm_num [h] at hs1
  have h0 : LFunction χ s ≠ 0 := fun hL => by
    have ⟨a, b⟩ := zeroStrip hpx h1 (by grind [norm_zero]) hne1 hL
    have := h s ⟨a, b, by simp, hL⟩
    simp at this
    linarith
  have hloc := localLemma hpx h0 hne1 h1 h2
  set t := im s
  have := half_le_LN N t
  obtain ⟨hf, hfw⟩ := zerosWindow hpx t
  rw [finsum_mem_eq_finite_toFinset_sum _ hf] at hloc hfw
  rw [← sub_neg_eq_add] at hloc
  grw [← norm_sub_norm_le, norm_neg, ← norm_sub_norm_le, ← norm_sub_norm_le,
    norm_sum_le, sum_le_sum (g := fun ρ => mR χ ρ / inv K), ← sum_div, div_inv_eq_mul, hfw,
    norm_div, ← hs0, mC0_le hpx t, norm_div, ← hs1, norm_del1 (χ := χ)] at hloc
  norm_num at hloc
  linarith
  intro ρ hrx
  rw [norm_div, norm_natCast]
  gcongr
  exact h ρ $ mp (mem_toFinset hf) hrx
end PrimSec

lemma one_lt_cLine_ef {u} (hu : 2 ≤ u := by linarith) : 1 < cLine u := by
  rw [cLine]
  linarith [mpr inv_pos $ log_pos $ by linarith]

lemma cLine_le_three_ef {u} (hu : 2 ≤ u := by linarith) : cLine u ≤ 3 := by
  rw [cLine]
  have := half_le_log hu
  grw [inv_anti₀ _ this] <;> norm_num

section RectSec
variable {x0 x1 y0 y1 : ℝ}

def rectBdry (x0 x1 y0 y1 : ℝ) : Set ℂ :=
  {s | (re s ∈ uIcc x0 x1 ∧ (im s = y0 ∨ im s = y1)) ∨ (im s ∈ uIcc y0 y1 ∧ (re s = x0 ∨ re s = x1))}

def rectOpen (x0 x1 y0 y1 : ℝ) : Set ℂ :=
  {s | x0 < re s ∧ re s < x1 ∧ y0 < im s ∧ im s < y1}

lemma bdryH {x y} (hx : x ∈ uIcc x0 x1) (hy : y = y0 ∨ y = y1) : cpx x y ∈ rectBdry x0 x1 y0 y1 :=
  inl ⟨hx, hy⟩

lemma bdryV {x y} (hy : y ∈ uIcc y0 y1) (hx : x = x0 ∨ x = x1) : cpx x y ∈ rectBdry x0 x1 y0 y1 :=
  inr ⟨hy, hx⟩

lemma hdH y x : HasDerivAt (cpx · y) 1 x := by
  simpa [← mk_eq_add_mul_I] using (hasDerivAt_id x).ofReal_comp.add_const $ cR y * I

lemma hdV x y : HasDerivAt (cpx x ·) I y := by
  simpa [← mk_eq_add_mul_I] using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add $ cR x

lemma seg {F f : ℂ → ℂ} {γ : ℝ → ℂ} {a b d s} (hγ : ∀ t, HasDerivAt γ d t)
    (h : ∀ t ∈ uIcc a b, HasDerivAt F (f (γ t)) (γ t)) (hc : ContinuousOn f s) (hs : ∀ t ∈ uIcc a b,
                                                                                γ t ∈ s) :
    d • ∫ t in a..b, f (γ t) = F (γ b) - F (γ a) := by
  rw [← integral_smul]
  exact integral_eq_sub_of_hasDerivAt (fun t ht => ((h t ht).comp t $ hγ t).congr_deriv $ mul_comm _ _)
    ((hc.comp (fun t _ => (hγ t).continuousAt.continuousWithinAt) hs).const_smul d).intervalIntegrable

lemma bdry_ne {s p} (hs : s ∈ rectBdry x0 x1 y0 y1) (hp : p ∈ rectOpen x0 x1 y0 y1) : s ≠ p := by
  rintro rfl
  grind [rectBdry, rectOpen]

lemma bdry_sub (hre : x0 ≤ x1 := by linarith) (him : y0 ≤ y1 := by linarith) : rectBdry x0 x1 y0 y1 ⊆ rect x0 x1 y0 y1 := by
  rintro s (⟨hr, hi | hi⟩ | ⟨hi,
                             hr | hr⟩) <;> rw [uIcc_of_le $ by assumption] at * <;> simp_all [rect,
                                                                                              mem_reProdIm]

lemma closed_nhds {p} (hp : p ∈ rectOpen x0 x1 y0 y1) : rect x0 x1 y0 y1 ∈ 𝓝 p :=
  mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds ⟨⟨hp.1, hp.2.1⟩,
                                                              hp.2.2⟩) fun _ h => ⟨Ioo_subset_Icc_self h.1, Ioo_subset_Icc_self h.2⟩

lemma rectInt_congr {f g} (h : EqOn f g (rectBdry x0 x1 y0 y1)) : rectInt f x0 x1 y0 y1 = rectInt g x0 x1 y0 y1 := by
  simp [rectInt]
  rw [integral_congr fun _ hx => h $ bdryH hx $ inl rfl,
      integral_congr fun _ hx => h $ bdryH hx $ inr rfl,
    integral_congr fun _ hy => h $ bdryV hy $ inr rfl, integral_congr fun _ hy => h $ bdryV hy $ inl rfl]

lemma rectInt_add {f g} (hf : ContinuousOn f (rectBdry x0 x1 y0 y1)) (hg : ContinuousOn g (rectBdry x0 x1 y0 y1)) :
    rectInt (fun s => f s + g s) x0 x1 y0 y1 = rectInt f x0 x1 y0 y1 + rectInt g x0 x1 y0 y1 := by
  have bi {γ : ℝ → ℂ} {a b} (h : ∀ t ∈ uIcc a b,
                             γ t ∈ rectBdry x0 x1 y0 y1) (hγ : Continuous γ := by
                                                                                                      simp_rw [mk_eq_add_mul_I]
                                                                                                      fun_prop) :=
    integral_add ((hf.comp hγ.continuousOn h).intervalIntegrable (μ := volume)) (hg.comp hγ.continuousOn h).intervalIntegrable
  simp at bi
  simp [rectInt, bi fun _ hx => bdryH hx $ inl rfl, bi fun _ hx => bdryH hx $ inr rfl,
    bi fun _ hy => bdryV hy $ inr rfl, bi fun _ hy => bdryV hy $ inl rfl]
  ring

lemma rectInt_div_sub {h p} (hp : p ∈ rectOpen x0 x1 y0 y1) (hh : DifferentiableOn ℂ h (rect x0 x1 y0 y1)) :
    rectInt (fun s => h s / (s - p)) x0 x1 y0 y1 = τI * h p := by
  have ⟨h1, h2, h3, h4⟩ := hp
  have hd := mpr (differentiableOn_dslope $ closed_nhds hp) hh
  have hc : ContinuousOn (fun s => inv $ s - p) _ :=
    ContinuousOn.inv₀ (by fun_prop) fun _ hs => sub_ne_zero_of_ne $ bdry_ne hs hp
  rw [rectInt_congr (g := fun s => dslope h p s + h p * inv (s - p)) fun s hs => by
        have hne := bdry_ne hs hp
        simp [dslope_of_ne _ hne, slope_def_field]
        field [sub_ne_zero_of_ne hne],
    rectInt_add (hd.continuousOn.mono bdry_sub) $ hc.const_mul $ h p,
    show rectInt (dslope h p) x0 x1 y0 y1 = 0 by
      simpa [rectInt, ← mk_eq_add_mul_I] using
        integral_boundary_rect_eq_zero_of_differentiableOn (dslope h p) ⟨x0, y0⟩ ⟨x1, y1⟩ $ by
          rwa [uIcc_of_le, uIcc_of_le]
          all_goals linarith,
    zero_add, rectInt]
  simp only [integral_const_mul, ← mul_smul_comm, ← mul_sub, ← mul_add]
  rw [mul_comm]
  congr 1
  have hL {s} (hs : s - p ∈ slitPlane) : HasDerivAt (fun s => Complex.log $ s - p) (inv $ s - p) s := by simpa using ((hasDerivAt_id s).sub_const p).clog hs
  have hH {y} (hy : y = y0 ∨ y = y1) (hy' : y - im p ≠ 0) :=
    seg (hdH y) (fun _ _ => hL $ mpr mem_slitPlane_iff $ inr hy') hc fun _ hx => bdryH hx hy
  simp_rw [one_smul] at hH
  rw [hH (inl rfl) $ by linarith, hH (inr rfl) $ by linarith,
    seg (hdV x1) (fun _ _ => hL $ mpr mem_slitPlane_iff $ inl $ by
                                                                   simp
                                                                   linarith) hc fun _ hy => bdryV hy $ inr rfl,
    seg (hdV x0) (fun _ _ => (((hasDerivAt_id _).const_sub p).clog $ mpr mem_slitPlane_iff $ inl $ by
                                                                                                      simp
                                                                                                      linarith).congr_deriv $ by
      rw [neg_div, ← div_neg, neg_sub, one_div]
      rfl) hc fun _ hy => bdryV hy $ inl rfl]
  apply cext <;> simp [log_re, log_im, norm_sub_rev]
  ring1
  rw [← neg_sub $ cpx x0 y1, ← neg_sub $ cpx x0 y0,
    arg_neg_eq_arg_sub_pi_of_im_pos, arg_neg_eq_arg_add_pi_of_im_neg]
  ring1
  all_goals simp
  all_goals linarith
end RectSec

section KernelSec

theorem perron_kernel_single_term_ef {y c T} (hy : 0 < y) (hc : 1 ≤ c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  set l := log y
  set E := y ^ c
  let ker s := cexp (l * s) / s
  set J := ∫ t in -T..T, ker (cpx c t)
  have hEe  := rpow_def_of_pos hy c
  have hE0 := hEe ▸ exp_pos _
  suffices hJ : ‖J - if 1 ≤ y then τ else 0‖ ≤ 2 * π * E * kb T y by
    have hP : perronK y c T = inv τ * J := by
      unfold perronK
      congr 1
      refine integral_congr fun t _ => ?_
      simp [ker, cpow_def_of_ne_zero (mpr ofReal_ne_zero hy.ne'), ← ofReal_log hy.le, l]
    rw [show (if 1 ≤ y then 1 else 0) = inv τ * if 1 ≤ y then τ else 0 by
          split_ifs <;> field [pi_ne_zero], hP, ← mul_sub, norm_mul]
    grw [hJ]
    simp
    field_simp
    rfl
  have hker x y : ‖ker (cpx x y)‖ = rexp (l * x) / ‖cpx x y‖ := by simp [ker, norm_exp]
  have hT0 := le_of_lt hT
  have h1 : ‖J - if 1 ≤ y then τ else 0‖ ≤ 2 * π * E * (1 + arsinh T) := by
    grw [norm_sub_le, norm_int_inv_sqrt (C := E) hT0]
    have := mul_nonneg hE0.le (mpr arsinh_nonneg_iff hT0)
    split_ifs with hy1 <;> simp
    nlinarith [pi_gt_three, one_le_rpow hy1 $ show 0 ≤ c by linarith]
    nlinarith [pi_gt_three]
    intro t _
    rw [hker, ← hEe, div_eq_mul_inv]
    gcongr
    rw [norm_def, normSq_mk]
    apply sqrt_le_sqrt
    nlinarith
  by_cases hl : l = 0
  simpa [kb, l, hl] using h1
  rw [kb, ite_eq_right hl, mul_min_of_nonneg]
  refine le_min h1 ?_
  set B := E / abs l / T
  have : 0 < B := by positivity
  set U := c + 1 + 2 * T / B
  have hcU : c < U := by linarith [show 0 < 2 * T / B by positivity]
  have hfin a b x sgn {L : ℂ}
      (h : I * L = sgn * ((∫ t in a..b, ker ⟨t, -T⟩) - ∫ t in a..b,
                          ker (cpx t T)) + I * ∫ t in -T..T, ker (cpx x t))
      (hab : a ≤ b := by linarith) (hm1 : l * a ≤ l * c := by nlinarith) (hm2 : l * b ≤ l * c := by nlinarith)
      (hlx : l * x ≤ 0 := by nlinarith) (hxU : abs x = U := by simp [show 0 ≤ U by linarith]) (hsgn : norm sgn = 1 := by simp) :
      norm L ≤ 2 * π * E * inv (T * abs l) := by
    have hh h (hh : abs h = T := by simp [hT0]) : ‖∫ t in a..b, ker (cpx t h)‖ ≤ B := by
      grw [norm_integral_le_of_norm_le (g := fun t => rexp (l * t) / T) hab _ $ Continuous.intervalIntegrable (by fun_prop) _ _]
      rw [integral_div, integral_comp_mul_left rexp hl, integral_exp, smul_eq_mul]
      simp [B]
      gcongr
      apply le_trans $ le_abs_self _
      rw [abs_mul, abs_inv, ← div_eq_inv_mul]
      gcongr
      grind [exp_pos $ l * b, exp_pos $ l * a, mpr exp_le_exp hm1, mpr exp_le_exp hm2]
      apply of_forall
      intro t _
      rw [hker]
      gcongr
      exact hh ▸ abs_im_le_norm (cpx t h)
    rw [show norm L = ‖I * L‖ by simp, h]
    grw [norm_add_le, norm_mul, hsgn, one_mul, norm_sub_le, hh $ -T, hh T, norm_mul, norm_I,
         one_mul,
      norm_integral_le_of_norm_le_const (C := rexp (l * x) / U), mpr exp_le_one_iff hlx,
      ← show 2 * T / B ≤ U by
                              dsimp [U]
                              linarith]
    rw [abs_of_pos $ by linarith]
    dsimp [B]
    field_simp
    nlinarith [pi_gt_three]
    intro t _
    rw [hker]
    gcongr
    exact hxU ▸ abs_re_le_norm (cpx x t)
  rcases lt_or_gt_of_ne hl with hneg | hpos
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn ker ⟨c, -T⟩ ⟨U, T⟩ fun z hz =>
    (DifferentiableAt.div (by fun_prop) differentiableAt_id $ by
      rintro rfl
      simp [uIcc_of_le hcU.le, mem_reProdIm] at hz
      linarith).differentiableWithinAt
  simp only [smul_eq_mul, ← mk_eq_add_mul_I] at hrect
  rw [ite_eq_right $ mpr not_le $ mp (log_neg_iff hy) hneg, sub_zero]
  apply hfin c U U 1
  linear_combination -hrect
  have hrect := rectInt_div_sub (h := fun s => cexp $ l * s) (p := 0) (x0 := -U) (x1 := c) (y0 := -T) (y1 := T)
    (by simp [rectOpen]
        grind) $ by fun_prop
  simp [rectInt] at hrect
  rw [ite_eq_left (mp (log_pos_iff hy.le) hpos).le]
  apply hfin (-U) c (-U) $ -1
  simp at *
  linear_combination hrect
  positivity
end KernelSec

section SidesSec
variable {u T T' : ℝ} (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T') (hT'1 : T' ≤ T + 1)
include hT hTu hTT' hT'1

theorem perronL :
    ‖psiRaw χ u - vertInt χ u T'‖ ≤ 1500 * Err N u T := by
  have hu := le_trans hT hTu
  have hc1 := one_lt_cLine_ef hu
  set c := cLine u
  have hu0 : 0 < u := by linarith
  let a : ℕ → ℂ := (fun n : ℕ => χ n) * fun n => (Λ n : ℂ)
  have ha n : ‖a n‖ ≤ Λ n := by
    simp [a, abs_of_nonneg vonMangoldt_nonneg]
    grw [norm_le_one χ _]
    simp
  have hT'0 : 0 < T' := by linarith
  set L := log u
  have := half_le_log hu
  have := mpr arsinh_nonneg_iff hT'0.le
  have hkb_nn y : 0 ≤ kb T' y := by
    unfold kb
    split_ifs <;> positivity
  have hkb_le {y a} (ha : 0 < a) (h : a ≤ abs (log y)) : kb T' y ≤ inv (T' * a) := by
    unfold kb
    rw [ite_eq_right $ by grind]
    grw [min_le_right]
    apply inv_anti₀ (by positivity)
    gcongr
  let pTerm n := Λ n * (u / n) ^ cLine u * kb T' (u / n)
  have hp_nn n : 0 ≤ pTerm n := mul_nonneg (mul_nonneg vonMangoldt_nonneg $ by positivity) $ hkb_nn _
  have hsumK M : ∑ n ∈ range M, pTerm n ≤ 1500 * (u * L ^ 2 / T' + L) := by
    let P n := rN n ≤ u / 2 ∨ 2 * u ≤ n
    set SF2 := (range M).filter (¬P ·)
    rw [← sum_filter_add_sum_filter_not (range M) P pTerm]
    refine le_trans (add_le_add (b := 40 * u * L ^ 2 / T') (d := 16 * L * (2 + 8 * L + 2 * (6 * u * L / T'))) ?_ ?_)
      (by field_simp
          nlinarith [mul_le_mul_of_nonneg_right (by linarith : T' ≤ 2 * u) $ sq_nonneg L])
    let e := inv $ 2 * L
    have hep : 0 < e := by positivity
    grw [sum_le_sum (g := fun n => 5 * u / T' / e * rN n ^ (-(e + 1))),
      ← mul_sum, sum_le_sum_of_subset_of_nonneg $ filter_subset _ _,
      (mpr summable_nat_rpow $ by linarith).sum_le_tsum $ range M, tsum_rpow_le]
    rw [add_sub_cancel_right]
    dsimp [e]
    field_simp
    nlinarith
    linarith
    intros
    positivity
    intros
    positivity
    intro n hn
    rcases eq_zero_or_pos n with rfl | hnp
    simp [pTerm]
    positivity
    have hx : 0 < rN n := mpr cast_pos hnp
    have := hkb_nn $ u / n
    dsimp [pTerm]
    grw [vonMangoldt_le_log, log_le_rpow_div hx.le hep, hkb_le (a := 0.69)]
    rw [div_rpow hu0.le hx.le, rpow_cLine_ef hu]
    grw [le_of_lt exp_one_lt_three]
    rw [show e + 1 = cLine u - e by
          dsimp [cLine, e]
          field, neg_sub, rpow_sub hx]
    field_simp
    nlinarith [show 0 ≤ u * rN n ^ e by positivity]
    norm_num
    focus
      rcases (mp mem_filter hn).2 with h | h
      rotate_left
      rw [← abs_neg, ← log_inv, inv_div]
      all_goals
        grw [← le_abs_self]
        apply half_le_log
        rw [le_div_iff₀] <;> linarith
    have hS2 n (hn : n ∈ SF2) : u / 2 < n ∧ n < 2 * u := by grind
    let f n := if n ∈ SF2 then kb T' (u / n) else 0
    grw [sum_le_sum (g := fun n => 16 * L * f n), ← mul_sum]
    gcongr
    set n0 := ⌊u⌋₊
    have : arsinh T' ≤ 4 * L := by
      grw [arsinh_le_log, show 1 + 2 * T' ≤ u ^ 4 by nlinarith [sq_nonneg $ u - 2]]
      simp [L]
    have hf6 m : f m ≤ 1 + 4 * L := by
      dsimp [f, kb]
      split_ifs <;> (try grw [min_le_left]) <;> linarith
    have hstep (g : ℕ → ℕ) (hg : ∀ j ∈ range n0,
                            j + 1 ≤ u - g j ∨ j + 1 ≤ g j - u) : ∑ j ∈ range n0, f (g j) ≤ 6 * u * L / T' := by
      grw [sum_le_sum (g := fun j => 2 * u / T' * inv (rN j + 1)), ← mul_sum, show ∑ j ∈ range n0,
           inv (rN j + 1) ≤ 3 * L by
        have := harmonic_le_one_add_log n0
        simp [harmonic] at this
        linarith [log_le_log (by linarith [lt_floor_add_one u]) $ floor_le hu0.le]]
      grind
      intro j hj
      dsimp [f]
      split_ifs with hm
      obtain ⟨hx1, hx2⟩ := hS2 _ hm
      have : 0 < rN (g j) := by linarith
      grw [hkb_le (a := (rN j + 1) / (2 * u)) $ by positivity]
      field_simp
      rfl
      rcases hg j hj with h | h
      grw [← le_abs_self, ← one_sub_inv_le_log_of_pos]
      field_simp
      nlinarith
      positivity
      grw [← neg_le_abs, le_neg, log_le_sub_one_of_pos]
      field_simp
      nlinarith
      positivity
      positivity
    grw [sum_le_sum_of_subset_of_nonneg (t := range $ n0 + (n0 + 2))]
    rw [sum_range_add, sum_range_succ', sum_range_succ', ← sum_range_reflect f n0]
    linarith [hf6 $ n0 + 0, hf6 $ n0 + (0 + 1),
      hstep (fun j => n0 - 1 - j) fun j hj => inl $ by
        have := mp mem_range hj
        rw [Nat.sub_sub, cast_sub $ by omega]
        push_cast
        linarith [floor_le hu0.le],
      hstep (fun j => n0 + (j + 1 + 1)) fun j _ => inr $ by
        push_cast
        linarith [lt_floor_add_one u]]
    intro n hn
    rw [mem_range, ← cast_lt (α := ℝ)]
    push_cast
    linarith [(hS2 n hn).2, lt_floor_add_one u]
    intro _ _ _
    dsimp [f]
    split_ifs
    exact hkb_nn _
    rfl
    intro n hn
    obtain ⟨hgt, hlt⟩ := hS2 n hn
    have hx : 0 < rN n := by linarith
    have := hkb_nn $ u / n
    dsimp [pTerm, f]
    rw [ite_eq_left hn]
    grw [vonMangoldt_le_log, log_le_2log $ show rN n ≤ u ^ 2 by nlinarith,
         mpr (div_le_iff₀ hx) (by linarith : u ≤ 2 * n), cLine_le_three_ef hu]
    linarith
    norm_num
  have hLsum := (LSeriesSummable_vonMangoldt (s := c) $ by simpa using hc1).norm
  let z t := cpx c t
  let K t := (u : ℂ) ^ z t / z t
  have hterm n t : ‖term a (z t) n‖ ≤ ‖term (fun k => (Λ k : ℂ)) c n‖ := by
    simp [norm_term_eq, z]
    split_ifs
    rfl
    grw [ha n, ← le_abs_self]
  have hEq n : a n * perronK (u / n) c T' = inv τ * ∫ t in (-T')..T', term a (z t) n * K t := by
    rcases eq_or_ne n 0 with rfl | hn
    simp [a]
    rw [perronK, mul_left_comm, ← integral_const_mul]
    congr 2
    funext t
    rw [term_of_ne_zero hn, ofReal_div, div_cpow_ofReal_nonneg hu0.le n.cast_nonneg]
    push_cast
    ring
  have hint t : -ldL χ (cpx (cLine u) t) = LSeries a (z t) := by
    simp [a, LSeries_twist_vonMangoldt_eq χ (s := z t) hc1, ldL, logDeriv_apply,
          deriv_LFunction_eq_deriv_LSeries χ (s := z t) hc1, LFunction_eq_LSeries χ (s := z t) hc1, neg_div, z, c]
  have hG : HasSum (fun n => a n * perronK (u / n) c T') $ vertInt χ u T' := by
    simp_rw [hEq, vertInt, hint]
    apply HasSum.mul_left
    apply intervalIntegral.hasSum_integral_of_dominated_convergence fun n _ => ‖term (fun k => (Λ k : ℂ)) c n‖ * (u ^ c / c)
    intro n
    by_cases hn : n = 0 <;> simp [hn, z, K, mk_eq_add_mul_I] <;> fun_prop
    intro n
    apply of_forall
    intro t _
    grw [norm_mul, hterm n t, norm_div, norm_cpow_eq_rpow_re_of_pos hu0]
    gcongr
    exact re_le_norm $ z t
    exact of_forall fun _ _ => hLsum.mul_right _
    exact intervalIntegrable_const
    exact of_forall fun t _ => (hLsum.of_norm_bounded (hterm · t)).hasSum.mul_right _
  have hind : HasSum (fun n => a n * if 1 ≤ u / n then 1 else 0) $ psiRaw χ u := by
    rw [psiRaw, sum_congr rfl fun n hn => ?_]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp [mem_Icc] at hn
    cases n
    simp [a]
    rw [ite_eq_right $ mpr not_le $ mpr (div_lt_one $ mpr cast_pos $ succ_pos _) $ lt_of_floor_lt $ hn $ succ_pos _, mul_zero]
    rw [mem_Icc] at hn
    simp [a, mpr (one_le_div $ mpr cast_pos hn.1) $ le_trans (mpr cast_le hn.2) $ floor_le hu0.le,
          mul_comm]
  unfold Err
  rw [← (hind.sub hG).tsum_eq]
  grw [tsum_of_norm_bounded (summable_of_sum_range_le hp_nn hsumK).hasSum,
       tsum_le_of_sum_range_le hp_nn hsumK, hTT']
  dsimp [L]
  gcongr <;> nlinarith [show u ≤ N * u by nlinarith [one_le_N N],
                        log_nonneg $ show 1 ≤ u by linarith]
  intro n
  rw [← mul_sub, norm_mul]
  cases n
  simp [a, pTerm]
  rw [norm_sub_rev]
  grw [ha _, perron_kernel_single_term_ef (div_pos hu0 $ mpr cast_pos $ succ_pos _) hc1.le,
       ← mul_assoc]
  linarith

section
variable (hpx : IsPrimitive χ) (hgood : GoodHeight χ T')
include hpx hgood

abbrev riR f u T' := rectInt f (-0.5) (cLine u) (-T') T'

omit hT'1 in
lemma shiftResidue :
    ‖riR (fun s => ldL χ s * (cR u ^ s / s)) u T' / τI
      - (zsum χ T' u + mC χ 0 * log u - del1 χ * (u - 1))‖ ≤ 6400 * log (2 * N) + S1 χ := by
  have hc := one_lt_cLine_ef $ le_trans hT hTu
  have hfin := zerosFinite_ef χ T'
  set S := toFinset hfin
  let mc := mC χ
  let B := rectBdry (-0.5) (cLine u) (-T') T'
  let K := rect (-0.5) (cLine u) (-T') T'
  let O := rectOpen (-0.5) (cLine u) (-T') T'
  have hNO {ρ} (h1 : 0 < re ρ) (h2 : re ρ < 1) (h3 : LFunction χ ρ = 0) (heq : aim ρ = T') : False := by
    have := hgood ρ h1 h2 h3
    norm_num [heq, mul_nonpos_iff] at this
    linarith [half_le_log (x := rN N * T') $ by nlinarith [one_le_N N]]
  have h0 : 0 ∈ O := by
    simp [O, rectOpen]
    grind
  have h1 : 1 ∈ O := by
    simp [O, rectOpen]
    grind
  have h0K := mem_of_mem_nhds $ closed_nhds h0
  obtain ⟨Z, g, hZ, hg, hg0, hfac⟩ := extract_zeros_Lent χ (isCompact_Icc.reProdIm isCompact_Icc)
    (by convert (convex_convexHull ℝ K).isPreconnected
        dsimp [K, rect]
        rw [convexHull_reProdIm, (convex_Icc _ _).convexHull_eq, (convex_Icc _ _).convexHull_eq])
    ⟨0, h0K, 1, mem_of_mem_nhds $ closed_nhds h1, zero_ne_one⟩
  have hZeq : Z.erase 0 = S := by
    ext s
    simp [hZ, S, mem_reProdIm, ← abs_le]
    constructor
    rintro ⟨hs0, ⟨⟨hx0, _⟩, hy⟩, hz⟩
    have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero_ef χ $ e ▸ hz
    rw [Lent_eq_zero_iff_ef hs1] at hz
    have ⟨a, b⟩ := zeroStrip hpx hx0 hs0 hs1 hz
    exact ⟨a, b, lt_of_le_of_ne hy $ hNO a b hz, hz⟩
    rintro ⟨a, b, c, d⟩
    exact ⟨by grind [zero_re], by grind, mpr (Lent_eq_zero_iff_ef $ by grind [one_re]) d⟩
  let H := logDeriv g
  have hHd : DifferentiableOn ℂ H K := fun s hs => ((hg s hs).deriv.differentiableAt.div (hg s hs).differentiableAt $ hg0 s hs).differentiableWithinAt
  have hHeq {s} (hs : s ∈ K) (hL0 : LFunction χ s ≠ 0) (hs1 : s ≠ 1) :
      ldL χ s = H s + (∑ ρ ∈ S, mc ρ / (s - ρ)) + mc 0 / s - del1 χ / (s - 1) := by
    rw [logDeriv_Lent_ef hs1 hL0, logDeriv_prod_factor (hfac s hs)
      (fun ρ hrx e => hL0 $ mp (Lent_eq_zero_iff_ef hs1) $ mp sub_eq_zero e ▸ (mp (hZ ρ) hrx).2) (hg0 s hs) (hg s hs).differentiableAt]
    dsimp [mc]
    by_cases h0Z : (0 : ℂ) ∈ Z
    rw [← add_sum_erase _ _ h0Z, hZeq]
    ring
    rw [← erase_eq_of_notMem h0Z, hZeq, mC0_zero fun h => h0Z $ mpr (hZ 0) ⟨h0K, h⟩]
    ring
  let E (s : ℂ) := cR u ^ s
  have hd s : HasDerivAt E (E s * Complex.log u) s := (hasStrictDerivAt_const_cpow $ inl $ mpr ofReal_ne_zero $ by linarith).hasDerivAt
  have hE : DifferentiableOn ℂ E K := fun s _ => (hd s).differentiableAt.differentiableWithinAt
  have hc_div {p} (hp : p ∈ O) {q} (hq : DifferentiableOn ℂ q K) : ContinuousOn (fun s => q s / (s - p)) B :=
    (hq.continuousOn.mono bdry_sub).div (by fun_prop) fun _ hs => sub_ne_zero_of_ne $ bdry_ne hs hp
  have hSmem ρ (hrx : ρ ∈ S) : ρ ≠ 0 ∧ ρ ∈ O := by
    simp [S, O, rectOpen, ZerosBelow, abs_lt] at hrx ⊢
    exact ⟨by
              rintro rfl
              simp at hrx, by linarith, by linarith, hrx.2.2.1⟩
  have hc2 : ContinuousOn (fun s => -mc 0 * -inv (s ^ 2)) B :=
    ((ContinuousOn.inv₀ (by fun_prop) fun _ hs => pow_ne_zero 2 $ bdry_ne hs h0).neg).const_mul _
  have hi0 : riR (fun s => -mc 0 * -inv (s ^ 2)) u T' = 0 := by
    have hH {y} (hy : y = -T' ∨ y = T') := seg (hdH y) (fun _ hx => (hasDerivAt_inv $ bdry_ne (bdryH hx hy) h0).const_mul $ -mc 0) hc2 fun _ hx => bdryH hx hy
    have hV {x} (hx : x = -0.5 ∨ x = cLine u) := seg (hdV x) (fun _ hy => (hasDerivAt_inv $ bdry_ne (bdryV hy hx) h0).const_mul $ -mc 0) hc2 fun _ hy => bdryV hy hx
    simp_rw [one_smul] at hH
    rw [riR, rectInt, hH $ inl rfl, hH $ inr rfl, hV $ inr rfl, hV $ inl rfl]
    ring
  let c0 : ℂ := ∑ ρ ∈ S, mc ρ / ρ
  let G s := H s * E s + (del1 χ - c0) * E s + mc 0 * dslope E 0 s
  let q ρ s := mc ρ * (E s / ρ) / (s - ρ)
  have hG : DifferentiableOn ℂ G K := ((hHd.mul hE).add $ hE.const_mul _).add $ (mpr (differentiableOn_dslope $ closed_nhds h0) hE).const_mul _
  have hEd ρ := (hE.div_const ρ).const_mul $ mc ρ
  have hEdc ρ (hrx : ρ ∈ S) := hc_div (hSmem ρ hrx).2 $ hEd ρ
  have hcG := hc_div h0 hG
  have hsc := continuousOn_finsetSum S hEdc
  have hc1 := hc_div h1 $ hE.const_mul $ -del1 χ
  have hsumS {W} (hW : W ⊆ S) : riR (fun s => ∑ ρ ∈ W,
                                     q ρ s) u T' = ∑ ρ ∈ W, τI * (mc ρ * (E ρ / ρ)) := by
    induction W using Finset.induction with
    | empty => simp [rectInt]
    | insert a U ha ih =>
      obtain ⟨haS, hU⟩ := mp Finset.insert_subset_iff hW
      simpa [q, sum_insert ha, rectInt_div_sub (hSmem a haS).2 $ hEd a, ih hU] using
        rectInt_add (hEdc a haS) $ continuousOn_finsetSum U fun ρ h => hEdc ρ $ hU h
  rw [show riR (fun s => ldL χ s * (cR u ^ s / s)) u T' = _ by
    dsimp [riR] at hsumS hi0
    rw [riR, rectInt_congr (g := fun s => (G s / (s - 0) + ∑ ρ ∈ S,
                                           q ρ s) + (-mc 0 * -inv (s ^ 2) + -del1 χ * E s / (s - 1))) fun s hsb => by
          have hs := (bdry_sub : B ⊆ K) hsb
          have hs0 := bdry_ne hsb h0
          have hs1 := bdry_ne hsb h1
          have hL : LFunction χ s ≠ 0 := fun h0' => by
            have ⟨a, b⟩ := zeroStrip hpx hs.1.1 hs0 hs1 h0'
            apply hNO a b h0'
            rcases hsb with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> grind
          dsimp [G]
          have hS : (∑ ρ ∈ S, mc ρ / (s - ρ)) * (E s / s) = (∑ ρ ∈ S, q ρ s) - c0 * E s / s := by
            simp [c0, q, sum_mul, sum_div, ← sum_sub_distrib]
            apply sum_congr rfl
            intro ρ hrx
            field [(hSmem ρ hrx).1, sub_ne_zero_of_ne $ bdry_ne hsb (hSmem ρ hrx).2]
          rw [hHeq hs hL hs1, dslope_of_ne _ hs0, slope_def_field, sub_zero, sub_mul, add_mul,
              add_mul, hS]
          simp [E, cpow_zero]
          field [sub_ne_zero_of_ne hs1],
      rectInt_add, rectInt_add, rectInt_add, rectInt_div_sub h0 hG, hsumS subset_rfl, ← mul_sum,
      hi0, rectInt_div_sub h1 $ hE.const_mul _]
    exacts [hc2, hc1, hcG, hsc, hcG.add hsc, hc2.add hc1]]
  obtain ⟨hZ0, hZ0sum⟩ := zerosWindow hpx 0
  let Zs := toFinset hZ0
  have hZsS : Zs ⊆ S := fun ρ hrx => by
    simp [Zs, S, ZerosNear, ZerosBelow] at hrx ⊢
    grind
  have hLN0 : LN N 0 = log (2 * N) := by grind
  let F z := H z + ∑ ρ ∈ S \ Zs, mc ρ / (z - ρ)
  have hFc : ContinuousAt F 0 := (hHd.continuousOn.continuousAt $ closed_nhds h0).add
    (tendsto_finsetSum (S \ Zs) fun ρ hrx => continuousAt_const.div (by fun_prop) $ by simp [(hSmem ρ $ sdiff_subset hrx).1])
  have hofR : Tendsto cR (𝓝[>] 0) $ 𝓝 0 := ofReal_zero ▸ continuous_ofReal.continuousWithinAt
  have hmain := le_of_tendsto (hFc.norm.tendsto.comp hofR) $ by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one, hofR.eventually_mem $ closed_nhds h0,
      hofR.eventually_mem $ hZ0.isClosed.isOpen_compl.mem_nhds $ by simp [ZerosNear]] with e ⟨he0,
                                                                                              he1x⟩ hre heZ
    have hLe : LFunction χ e ≠ 0 := fun h => heZ $ by
      simp [ZerosNear, h]
      grind
    have he1p : (e : ℂ) ≠ 1 := by
      simp
      linarith
    convert (by simpa using localLemma hpx (s := e) hLe he1p) using 2
    dsimp [F, Zs, mc]
    congr 1
    rw [hHeq hre hLe he1p, finsum_mem_eq_finite_toFinset_sum _ hZ0, ← sum_sdiff hZsS]
    ring1
  have hB1 : ZerosBelow χ 1 ⊆ ZerosNear χ 0 := fun ρ ⟨a, b, c, d⟩ => ⟨a, b, by simpa using c.le, d⟩
  have hB1f := hZ0.subset hB1
  have : ‖∑ ρ ∈ Zs, mc ρ / ρ‖ ≤ S1 χ + 132 * log (2 * N) := by
    grw [norm_sum_le]
    simp [Zs, mc]
    rw [← sum_sdiff $ toFinset_mono (hs := hB1f) hB1, ← finsum_mem_eq_finite_toFinset_sum _ hB1f,
        add_comm]
    grw [sum_le_sum (g := mR χ),
      sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => cast_nonneg _,
      ← finsum_mem_eq_finite_toFinset_sum _ hZ0, hZ0sum, hLN0]
    rfl
    intro ρ hrx
    simp [ZerosBelow, ZerosNear] at hrx
    apply div_le_self $ cast_nonneg _
    grind [abs_im_le_norm ρ]
  apply le_trans (le_of_eq $ congrArg norm _) $ (norm_sub_le (F 0) $ ∑ ρ ∈ Zs, mc ρ / ρ).trans _
  rw [ofReal_log, zsum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  dsimp [τI, F, G, c0, mc, E]
  rw [← sum_sdiff hZsS]
  simp [dslope_same, (hd 0).deriv, E, div_neg, sum_neg_distrib]
  field_simp [pi_ne_zero]
  ring1
  linarith
  linarith [hLN0 ▸ hmain, hLN0 ▸ half_le_LN N 0]

theorem shiftBound :
    ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ ≤ 10100000 * Err N u T + S1 χ := by
  have := one_le_N N
  have hu2 := le_trans hT hTu
  have hu0 : 0 < u := by linarith
  have hT'0 : 0 < T' := by linarith
  have := one_lt_cLine_ef hu2
  have := cLine_le_three_ef hu2
  let f s := ldL χ s * (u ^ s / s)
  let L := log $ N * u * T
  let LT2 := log $ N * (T' + 2)
  have : 2 ≤ N * u := by nlinarith
  have : 0 ≤ L := log_nonneg $ by nlinarith
  have : 0 ≤ LT2 := log_nonneg $ by nlinarith
  have hY2 : N * (4 * T ^ 2) ≤ (N * u * T) ^ 2 := by
    rw [← mul_assoc, mul_pow]
    gcongr
    nlinarith
  have hf4 : LT2 ≤ 2 * L := log_le_2log $ le_trans (by
                                                       gcongr
                                                       nlinarith) hY2
  have hhor h (hh : abs h = T') :
      ‖∫ x in -0.5..cLine u, f (cpx x h)‖ ≤ 4800000 * L ^ 2 * u / T := by
    grw [norm_integral_le_of_norm_le_const (C := 1350000 * L ^ 2 * u / T)]
    rw [abs_of_nonneg]
    field_simp
    nlinarith [sq_nonneg L]
    linarith
    intro x hx
    rw [uIoc_of_le $ by linarith] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [f, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hu0]
    have := half_le_log (x := N * T')
    have hkey := norm_logDeriv_le_ef hpx (s := cpx x h)
      (by linarith [hh ▸ abs_im_le_norm (cpx x h)])
      (by grw [← abs_im_le_norm]
          simp [hh]
          linarith)
      (by linarith) fun ρ ⟨a, b, _,
                           d⟩ => le_trans (hgood ρ a b d) $ by grind [abs_im_le_norm $ cpx x h - ρ,
                                                                      sub_im]
    simp [LN, hh] at hkey
    grw [show ‖ldL χ (cpx x h)‖ ≤ 450000 * L ^ 2 by
        nlinarith [hkey, hf4, show log (N * T') ≤ L from log_le_log (by nlinarith) $ by nlinarith],
      rpow_le_rpow_of_exponent_le _ hx2, rpow_cLine_ef hu2, le_of_lt exp_one_lt_three, ← hh.ge.trans $ abs_im_le_norm $ cpx x h, ← hTT']
    apply le_of_eq
    ring1
    linarith
  have hleft := norm_int_inv_sqrt (f := fun t => f ⟨-0.5, t⟩) (C := 14000 * LT2) hT'0.le fun t ⟨ht1,
                                                                                                ht2⟩ => by
    simp only [f, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hu0]
    have hkey := norm_logDeriv_le_ef hpx (s := ⟨-0.5, t⟩)
      (by grw [← abs_re_le_norm]
          norm_num)
      (by grw [← abs_re_le_norm]
          norm_num)
      two_pos fun ρ hrx => by
        grw [← abs_re_le_norm]
        simp
        grind [hrx.1]
    simp at hkey ⊢
    grw [hkey, show LN N t ≤ LT2 by
        apply log_le_log
        nlinarith [abs_nonneg t]
        gcongr
        exact mpr abs_le ⟨ht1.le, ht2⟩,
      rpow_le_one_of_one_le_of_nonpos,
      ← show √(1 + t ^ 2) / 2 ≤ ‖cpx (-0.5) t‖ by
        rw [norm_def, normSq_mk, ← sqrt_sq zero_le_two, ← sqrt_div $ by positivity]
        apply sqrt_le_sqrt
        nlinarith]
    field_simp
    all_goals linarith
  have hdiv : ‖(riR f u T' + τI * vertInt χ u T') / τI‖ ≤ 10000000 * Err N u T := by
    simp [τI]
    grw [div_le_self $ norm_nonneg _,
      nadd3 (hhor (-T') $ by simp [hT'0.le]) (nneg $ hhor T' $ by simp [hT'0.le])
        (by simpa using hleft : ‖-(I * _)‖ ≤ _) $ by
          simp [rectInt, vertInt, f, neg_mul, integral_neg]
          field_simp [pi_ne_zero]
          ring1]
    unfold Err
    grw [arsinh_le_log, log_le_2log $ le_trans (by nlinarith) hY2, hf4]
    dsimp [L]
    field_simp
    nlinarith [log_nonneg $ show 1 ≤ N * u by nlinarith,
               mul_le_mul_of_nonneg_right hTu $ sq_nonneg $ log $ N * u * T]
    linarith [pi_gt_three]
  have hm0 : ‖-(mC χ 0 * log u)‖ ≤ 132 * (u * L ^ 2 / T) := by
    have hlu0 := log_nonneg $ show 1 ≤ u by linarith
    rw [norm_neg, norm_mul, norm_real, norm_of_nonneg hlu0]
    grw [mC0_le hpx 0,
      show LN N 0 ≤ L from log_le_log (by simp [pos N]) $ by
        simp
        nlinarith,
      show log u ≤ L from log_le_log hu0 $ by nlinarith]
    rw [← mul_div_assoc, le_div_iff₀]
    nlinarith only [hTu, sq_nonneg L]
    linarith
  grw [nadd3 (le_trans (norm_add_le _ _) $ add_le_add hdiv $ nneg $ shiftResidue hT hTu hTT' hpx hgood) hm0 (nneg $ norm_del1 (χ := χ)) _]
  unfold Err
  linarith [half_le_log (x := N * u), show 0 ≤ u * log (N * u * T) ^ 2 / T by positivity,
    log_le_log (by nlinarith) (by nlinarith : 2 * N ≤ N * u)]
  dsimp [f, τI]
  field_simp [pi_ne_zero]
  ring1
end
end SidesSec

end EF

open EF

namespace EF

theorem explicitFormula :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
        ∀ u T : ℝ, 2 ≤ T → T ≤ u →
          ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}).Finite ∧
          ‖((∑ n ∈ Finset.Icc 1 ⌊u⌋₊,
             ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)) -
              (if χ = 1 then (u : ℂ) else 0)) +
            ∑ᶠ ρ ∈ ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}),
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
            C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
              ∑ᶠ ρ ∈ ({ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0}),
                (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖ρ‖) := by
  refine ⟨10102292, by norm_num, fun N _ χ hpx u T hT hTu => ?_⟩
  have hF := zerosFinite_ef χ T
  exists hF
  have hN1 := one_le_N N
  let th := T + 0.5
  set LT := log $ N * (T + 3)
  have hU := (zerosWindow hpx th).1.union (zerosWindow hpx $ -th).1
  set S := (toFinset hU).image aim
  have : rN (card S) ≤ 264 * LT := by
    grw [show rN (card S) ≤ card (toFinset hU) by exact_mod_cast card_image_le,
      ← sum_mult_le hpx _ fun _ => mp $ mem_toFinset hU]
    rw [card_eq_sum_ones, cast_sum]
    apply sum_le_sum
    intro ρ hrx
    simp [ZerosNear] at hrx
    have hne : ρ ≠ 1 := by grind [one_re]
    norm_cast
    rw [one_le_iff_ne_zero, mult, ← order_Lent_ef hne, ← natCast_ne_zero, ← div_Lent $ mem_univ ρ,
        div_Lent_ne_zero $ mem_univ ρ, Lent_eq_zero_iff_ef hne]
    grind
  let K := rN (card S) + 1
  have hK : 0 < K := by positivity
  obtain ⟨i, hi,
          hni⟩ := exists_mem_notMem_of_card_lt_card (s := S.image fun y => ⌊(y - T) * K⌋₊) (t := range $ card S + 1) $ by
    grw [card_image_le]
    simp
  let T' := T + (i + 0.5) / K
  have hT1 : T ≤ T' := le_add_of_nonneg_right $ by positivity
  have hT2 : T' ≤ T + 1 := by
    have : rN i ≤ card S := by
      norm_cast
      grind
    rw [add_le_add_iff_left, div_le_one hK]
    linarith
  have hg : GoodHeight χ T' := fun ρ h0 h1 hL => by
    have := half_le_log (x := rN N * T')
    have : LT ≤ 3 * log (N * T') := by
      dsimp [LT]
      grw [log_le_log _ $ show rN N * (T + 3) ≤ (N * T') ^ 3 by
        rw [mul_pow]
        gcongr
        exact le_self_pow₀ hN1 three_ne_zero
        nlinarith [sq_nonneg $ T' - 2]]
      simp [log_pow]
      nlinarith
    by_cases hw : abs (aim ρ - th) ≤ 1
    grw [inv_anti₀ (by positivity) (by linarith : 2 * K ≤ 1600 * log (N * T'))]
    refine le_of_not_gt fun hlt => hni $ mpr mem_image ⟨aim ρ,
                                                        mem_image_of_mem _ $ mpr (mem_toFinset hU) $ by by_cases hi' : 0 ≤ im ρ <;> [left; right] <;> exact ⟨h0, h1, by grind, hL⟩, ?_⟩
    have ⟨_, _⟩ := mp abs_lt hlt
    dsimp [T'] at *
    field_simp at *
    rw [floor_eq_iff]
    constructor <;> linarith
    linarith
    grind [inv_anti₀ two_pos $ show 2 ≤ 1600 * log (N * T') by linarith]
  have htc : ‖zsum χ T' u - zsum χ T u‖ ≤ 792 * Err N u T := by
    have hF' := zerosFinite_ef χ T'
    set D := toFinset hF' \ toFinset hF
    have hD ρ (hrx : ρ ∈ D) : 0 < re ρ ∧ re ρ < 1 ∧ T ≤ |im ρ| ∧ |im ρ| ≤ T + 1 ∧ LFunction χ ρ = 0 := by
      simp [D, ZerosBelow] at hrx
      grind
    unfold zsum Err
    rw [finsum_mem_eq_finite_toFinset_sum _ hF', finsum_mem_eq_finite_toFinset_sum _ hF,
      ← sum_sdiff $ toFinset_mono (hs := hF) (ht := hF') fun ρ h => ⟨h.1, h.2.1,
                                                                     h.2.2.1.trans_le hT1, h.2.2.2⟩, add_sub_cancel_right]
    have : 4 ≤ u * T := by nlinarith
    set L := log $ N * u * T
    have : 0.69 ≤ L := half_le_log
    have : 0 ≤ u / T := div_nonneg (by linarith) $ by linarith
    grw [norm_sum_le, sum_le_sum (g := fun ρ => mR χ ρ * (u / T)),
      ← sum_mul, sum_mult_le (T := T) hpx D,
      log_le_2log $ show rN N * (T + 3) ≤ (N * u * T) ^ 2 by
        rw [mul_assoc, mul_pow]
        gcongr <;> nlinarith]
    field_simp
    nlinarith [log_nonneg $ show 1 ≤ N * u by nlinarith, show 0 ≤ u * L by nlinarith]
    intro ρ hrx
    obtain ⟨a, b, c, d, e⟩ := hD ρ hrx
    by_cases hi : 0 ≤ im ρ <;> [left; right] <;> exact ⟨a, b, by grind, e⟩
    intro ρ hrx
    obtain ⟨_, b, c, _, _⟩ := hD ρ hrx
    rw [norm_mul, norm_div, norm_natCast, norm_cpow_eq_rpow_re_of_pos]
    grw [rpow_le_rpow_of_exponent_le _ b.le, rpow_one, ← le_trans c $ abs_im_le_norm ρ]
    all_goals linarith
  have : 0 ≤ S1 χ := finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  change ‖psiRaw χ u - (if χ = 1 then ↑u else 0) + zsum χ T u‖ ≤ _ * (Err N u T + S1 χ)
  grw [nadd3 (perronL (χ := χ) hT hTu hT1 hT2) (shiftBound hT hTu hT1 hT2 hpx hg) (nneg htc) _]
  linarith
  unfold del1
  split_ifs <;> ring1

end EF


public section

theorem zerosWindow_closed : PI.ZerosWindow :=
  ⟨132, by norm_num, fun _ _ _ hp t => by
    unfold PI.ZerosNear
    exact EF.zerosWindow hp t⟩

theorem explicitFormula_closed : PI.ExplicitFormula := by
  unfold PI.ExplicitFormula PI.ExplicitFormulaWith PI.psi0 PI.ZerosBelow
  convert EF.explicitFormula

end