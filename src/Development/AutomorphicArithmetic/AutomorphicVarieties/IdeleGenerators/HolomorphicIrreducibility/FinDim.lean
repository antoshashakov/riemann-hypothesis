module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq

@[expose] public section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af Filter Asymptotics Function
open scoped MatrixGroups ModularForm Topology

private theorem fd_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have hF := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hle : ((m : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF]
    intro i hi
    have hc := h i hi
    rw [qExpansion_coeff] at hc
    simpa [Nat.factorial_ne_zero] using hc
  obtain ⟨g, hg, hev⟩ := (natCast_le_analyticOrderAt hF).mp hle
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hev' : ∀ᶠ τ : ℍ in atImInfty,
      Periodic.qParam 1 τ ^ m * g (Periodic.qParam 1 τ) = f τ := by
    filter_upwards [hq.eventually hev] with τ hτ
    rw [← SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero, hτ, sub_zero, smul_eq_mul]
  have hb : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp hq).isBigO_one ℂ
  have key := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul hb
  simp only [mul_one] at key
  exact key.congr' hev' (Eventually.of_forall fun _ => rfl)

private theorem fd_order {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 :=
  GlobalTheory.EisM.qExpansion_coeff_zero_of_isBigO_qParam_pow hΓ f m h

private theorem fd_norm {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  letI := Fintype.ofFinite ((𝒮ℒ) ⧸ Γ.subgroupOf 𝒮ℒ)
  classical
  have hb : ∀ q : (𝒮ℒ) ⧸ Γ.subgroupOf 𝒮ℒ,
      SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q =O[atImInfty] (fun _ => (1 : ℂ)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      obtain ⟨_, γ, rfl⟩ := r
      rw [SlashInvariantForm.quotientFunc_mk]
      have hbd := ModularFormClass.bdd_at_infty_slash f γ⁻¹
      rw [ModularForm.SL_slash] at hbd
      have e : (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ :=
        (map_inv _ _).symm
      refine IsBigO.trans ?_ (isBigO_const_const (1 : ℝ) (one_ne_zero (α := ℂ)) atImInfty)
      simp only [Subgroup.coe_mk, e]
      exact hbd
  have hP : (fun τ => ∏ q ∈ Finset.univ.erase ⟦(1 : 𝒮ℒ)⟧,
      SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q τ) =O[atImInfty] (fun _ => (1 : ℂ)) := by
    simpa using IsBigO.finsetProd (s := Finset.univ.erase ⟦(1 : 𝒮ℒ)⟧) (fun q _ => hb q)
  refine IsBigO.congr ((isBigO_refl (⇑f) atImInfty).mul hP) (fun τ => ?_) (fun τ => mul_one _)
  rw [ModularForm.coe_norm, Finset.prod_apply,
    ← Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q τ)
      (Finset.mem_univ ⟦(1 : 𝒮ℒ)⟧)]
  simp [SlashInvariantForm.quotientFunc_mk]
  left
  convert rfl

private theorem fd_sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : CuspForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := fd_order one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _ ((fd_norm f).trans (fd_bigO hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem UpperTheory.V.Sd.finDim :
    UpperTheory.V.Sd.FinDim := by
  intro N k _
  have hΓ : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    simp
  obtain ⟨m, hm⟩ := fd_sturm hΓ (k : ℤ)
  refine ⟨?_, fun f hf => hm f fun n _ => ?_⟩
  · let L : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) (k : ℤ) →ₗ[ℂ]
        (Fin m → ℂ) :=
      { toFun := fun f i => (qExpansion 1 f).coeff i
        map_add' := fun f g => by
          ext i
          simp only [CuspForm.coe_add, ModularForm.qExpansion_add one_pos hΓ f g, map_add (f := _),
            Pi.add_apply]
        map_smul' := fun c f => by
          ext i
          simp only [CuspForm.coe_smul, ModularForm.qExpansion_smul one_pos hΓ c f,
            PowerSeries.coeff_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
    refine Module.Finite.of_injective L fun f g hfg => ?_
    have hfg0 : f - g = 0 := hm (f - g) fun n hn => by
      have hc := congrFun hfg ⟨n, hn⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hc
      rw [CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ f g, map_sub, hc, sub_self]
    exact sub_eq_zero.mp hfg0
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
    · exact hf n hn
