module

public import Formalism.SubspaceCounting.Statement
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.SubspaceCounting.SubspaceCountingProofs.ManyOrbits
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace CyclicSpanLengthLemmas

open ManyOrbitsP

private theorem length_eq_length_add_length_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z]
    (W : Submodule R Z) : Module.length R Z = Module.length R W + Module.length R (Z ⧸ W) :=
  Module.length_eq_add_of_exact W.subtype W.mkQ Subtype.val_injective W.mkQ_surjective
    (LinearMap.exact_subtype_mkQ W)

private theorem span_range_map_eq_univ_of_surjective {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {n : ℕ} (F : A →ₗ[R] B) (hF : Function.Surjective F)
    (g : Fin n → A) (hg : Submodule.span R (Set.range g) = ⊤) :
    Submodule.span R (Set.range (fun i => F (g i))) = ⊤ := by
  change Submodule.span R (Set.range (F ∘ g)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, hg, Submodule.map_top, LinearMap.range_eq_top.mpr hF]

private theorem length_le_mul_of_span_fin_pow_smul_eq_zero {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (k : ℕ) : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q]
    (g : Fin n → Q), Submodule.span R (Set.range g) = ⊤ → (∀ q : Q, π ^ k • q = 0) →
    Module.length R Q ≤ ((k * n : ℕ) : ℕ∞) := by
  intro n Q _ _ g hg hk
  classical
  let L (i : Fin n) := Submodule.span R {g i}
  let f := LinearMap.lsum R (fun i => ↥(L i)) R (fun i => (L i).subtype)
  have hf : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    rw [← top_le_iff, ← hg, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i ⟨g i, Submodule.mem_span_singleton_self _⟩,
      LinearMap.lsum_piSingle R _ R _ _ _⟩
  calc
    Module.length R Q ≤ Module.length R (∀ i, L i) := Module.length_le_of_surjective f hf
    _ = ∑ i, Module.length R (L i) := Module.length_pi_of_fintype R _
    _ ≤ ∑ _ : Fin n, (k : ℕ∞) :=
      Finset.sum_le_sum fun i _ => LengthLayersP.length_span_singleton_le π hπ k (g i) (hk (g i))
    _ = ((k * n : ℕ) : ℕ∞) := by simp [nsmul_eq_mul, mul_comm]

private theorem length_le_sum_of_antitone_chain_quot_le {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] :
    ∀ (V : ℕ) (E : ℕ → Submodule R Z) (b : ℕ → ℕ), E V = ⊥ → (∀ j, E (j + 1) ≤ E j) →
    (∀ j < V, Module.length R (E j ⧸ (E (j + 1)).comap (E j).subtype) ≤ (b j : ℕ∞)) →
    Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, b j : ℕ) : ℕ∞) := by
  intro V
  induction V with
  | zero =>
    intro E b hV _ _
    rw [hV, Module.length_bot]
    simp
  | succ V ih =>
    intro E b hV hE hb
    have h := ih (fun j => E (j + 1)) (fun j => b (j + 1)) hV (fun j => hE (j + 1))
      (fun j hj => hb (j + 1) (by omega))
    rw [LengthLayersP.length_eq_add_of_le (hE 0), Finset.sum_range_succ', Nat.cast_add]
    exact add_le_add h (hb 0 (by omega))

private theorem length_quot_comap_le_mul_of_pow_smul_mem {R Z : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup Z] [Module R Z] (π : R) (hπ : Irreducible π) (S n : ℕ) (E E' : Submodule R Z)
    (hEE : ∀ z ∈ E, π ^ S • z ∈ E') (g : Fin n → Z) (hg : E ≤ Submodule.span R (Set.range g)) :
    Module.length R (E ⧸ E'.comap E.subtype) ≤ ((S * n : ℕ) : ℕ∞) := by
  let B := Pi.basisFun R (Fin n)
  let ψ := B.constr R g
  have hrange : E ≤ LinearMap.range ψ := by
    simpa only [ψ, Module.Basis.constr_range] using hg
  obtain ⟨m, b⟩ := Submodule.basisOfPid B (E.comap ψ)
  have hm : m ≤ n := by
    have h := Submodule.finrank_le (E.comap ψ)
    simpa only [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] using h
  let Ψ : (E.comap ψ) →ₗ[R] E := (ψ.domRestrict (E.comap ψ)).codRestrict E (fun p => p.2)
  have hΨ : Function.Surjective Ψ := by
    intro e
    obtain ⟨r, hr⟩ := hrange e.2
    exact ⟨⟨r, by simp [hr]⟩, Subtype.ext hr⟩
  have hF := (Submodule.mkQ_surjective (E'.comap E.subtype)).comp hΨ
  have hsp := span_range_map_eq_univ_of_surjective ((E'.comap E.subtype).mkQ ∘ₗ Ψ) hF b b.span_eq
  have hkill (q : E ⧸ E'.comap E.subtype) : π ^ S • q = 0 := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hEE z.1 z.2
  calc
    Module.length R (E ⧸ E'.comap E.subtype) ≤ ((S * m : ℕ) : ℕ∞) :=
      length_le_mul_of_span_fin_pow_smul_eq_zero π hπ S m _ _ hsp hkill
    _ ≤ ((S * n : ℕ) : ℕ∞) := by exact_mod_cast Nat.mul_le_mul_left S hm

theorem lengthPart2 {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β < V, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ d * s ^ (β + 1) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * ((τ : ℝ) + 2 * S * s) := by
  classical
  set K : Submodule R M := Submodule.comap M.subtype (N ⊓ (Ideal.span {π ^ τ}) • M) with hKdef
  choose! C hCM hCcard hCx using h1
  set A0 : Submodule R (M ⧸ K) :=
    LinearMap.range ((π ^ τ) • (LinearMap.id : (M ⧸ K) →ₗ[R] (M ⧸ K))) with hA0def
  set bas := Module.finBasisOfFinrankEq R M hd with hbas
  have hQ : Module.length R ((M ⧸ K) ⧸ A0) ≤ ((τ * d : ℕ) : ℕ∞) := by
    refine length_le_mul_of_span_fin_pow_smul_eq_zero π hπ τ d ((M ⧸ K) ⧸ A0) (fun i => (A0.mkQ ∘ₗ K.mkQ) (bas i)) ?_ ?_
    · exact span_range_map_eq_univ_of_surjective (A0.mkQ ∘ₗ K.mkQ)
        ((Submodule.mkQ_surjective A0).comp (Submodule.mkQ_surjective K)) bas bas.span_eq
    · intro q
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective A0 q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨z, rfl⟩
  have hKθ : K ≤ LinearMap.ker (N.mkQ ∘ₗ M.subtype) := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_inf.mp (Submodule.mem_comap.mp hx)).1
  set θ : (M ⧸ K) →ₗ[R] X ⧸ N := K.liftQ (N.mkQ ∘ₗ M.subtype) hKθ with hθdef
  have hθmk : ∀ x : M, θ (Submodule.Quotient.mk x) = N.mkQ (x : X) := fun x => rfl
  set E : ℕ → Submodule R (X ⧸ N) := fun j => Submodule.map (N.mkQ ∘ₗ M.subtype)
    (LinearMap.range ((π ^ (τ + j * S)) • (LinearMap.id : M →ₗ[R] M))) with hEdef
  have hEmem : ∀ j (x : M), N.mkQ (π ^ (τ + j * S) • (x : X)) ∈ E j := fun j x =>
    Submodule.mem_map.mpr ⟨π ^ (τ + j * S) • x, LinearMap.mem_range.mpr ⟨x, rfl⟩, rfl⟩
  have hEcases : ∀ j, ∀ w ∈ E j, ∃ x : M, w = N.mkQ (π ^ (τ + j * S) • (x : X)) := by
    intro j w hw
    simp only [hEdef] at hw
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact ⟨x, rfl⟩
  have hAx : ∀ a : M ⧸ K, a ∈ A0 → ∃ x : M, a = Submodule.Quotient.mk (π ^ τ • x) := by
    intro a ha
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ha
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K w
    exact ⟨x, by rw [← hw, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_smul]⟩
  have hθA : ∀ a : A0, (θ ∘ₗ A0.subtype) a ∈ E 0 := by
    intro a
    obtain ⟨x, hx⟩ := hAx a a.2
    rw [LinearMap.comp_apply, Submodule.subtype_apply, hx, hθmk, Submodule.coe_smul]
    simpa using hEmem 0 x
  set θA : A0 →ₗ[R] E 0 := LinearMap.codRestrict (E 0) (θ ∘ₗ A0.subtype) hθA with hθAdef
  have hθinj : Function.Injective θA := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have ha' : θ (a : M ⧸ K) = 0 := congrArg Subtype.val ha
    obtain ⟨x, hx⟩ := hAx a a.2
    rw [hx, hθmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha'
    apply Subtype.ext
    rw [hx, Submodule.coe_zero, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr
      ⟨ha', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) x.2⟩)
  obtain ⟨C0, -, hC0card, hC0⟩ := h2
  have hC0e : C0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hC0card)
  have hEV : E V = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := hEcases V w hw
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hx' : π ^ (V * S) • (π ^ τ • (x : X)) ∈ N := by
      have h := hC0 (π ^ τ • (x : X)) (M.smul_mem _ x.2)
      rwa [hC0e, Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at h
    rwa [smul_smul, ← pow_add, add_comm (V * S) τ] at hx'
  have hEmono : ∀ j, E (j + 1) ≤ E j := by
    intro j w hw
    obtain ⟨x, rfl⟩ := hEcases (j + 1) w hw
    have e : π ^ (τ + (j + 1) * S) • (x : X) = π ^ (τ + j * S) • ((π ^ S • x : M) : X) := by
      rw [Submodule.coe_smul, smul_smul, ← pow_add]
      ring_nf
    rw [e]
    exact hEmem j _
  have hEstep : ∀ j, ∀ z ∈ E j, π ^ S • z ∈ E (j + 1) := by
    intro j z hz
    obtain ⟨x, rfl⟩ := hEcases j z hz
    have e : π ^ S • N.mkQ (π ^ (τ + j * S) • (x : X)) =
        N.mkQ (π ^ (τ + (j + 1) * S) • (x : X)) := by
      rw [← map_smul, smul_smul, ← pow_add]
      ring_nf
    rw [e]
    exact hEmem (j + 1) x
  have hEspan : ∀ j < V, E j ≤ Submodule.span R
      (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X))) := by
    intro j hj w hw
    obtain ⟨x, rfl⟩ := hEcases j w hw
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp (hCx j hj x x.2)
    have hmk : N.mkQ (π ^ (τ + j * S) • (x : X)) = N.mkQ c := by
      rw [← hnc, map_add (f := _), Submodule.mkQ_apply N n, (Submodule.Quotient.mk_eq_zero N).mpr hn,
        zero_add]
    rw [hmk]
    have hle : Submodule.map N.mkQ (Submodule.span R (↑(C j) : Set X)) ≤ Submodule.span R
        (Set.range (fun i : Fin (C j).card => N.mkQ (((C j).equivFin.symm i : C j) : X))) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨(C j).equivFin ⟨y, hy⟩, by simp⟩
    exact hle ⟨c, hc, rfl⟩
  have hE0 : Module.length R (E 0) ≤ ((∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞) :=
    length_le_sum_of_antitone_chain_quot_le V E (fun j => S * (C j).card) hEV hEmono
      (fun j hj => length_quot_comap_le_mul_of_pow_smul_mem π hπ S _ (E j) (E (j + 1)) (hEstep j) _ (hEspan j hj))
  have hA0 : Module.length R A0 ≤ Module.length R (E 0) :=
    Module.length_le_of_injective θA hθinj
  have hL : Module.length R (M ⧸ K) ≤
      ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℕ∞) := by
    rw [length_eq_length_add_length_quot A0, Nat.cast_add]
    exact (add_le_add (hA0.trans hE0) hQ).trans (le_of_eq (add_comm _ _))
  obtain ⟨ℓ, hℓ⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hL)
  refine ⟨ℓ, hℓ.symm, ?_⟩
  have hℓT : ℓ ≤ τ * d + ∑ j ∈ Finset.range V, S * (C j).card := by
    rw [← hℓ] at hL
    exact_mod_cast hL
  have hgeom : ∀ W : ℕ, ∑ j ∈ Finset.range W, s ^ (j + 1) ≤ 2 * s - 2 * s ^ (W + 1) := by
    intro W
    induction W with
    | zero => simp
    | succ W ih =>
      rw [Finset.sum_range_succ]
      have h3 : 0 ≤ s ^ (W + 1) * (1 - 2 * s) := mul_nonneg (pow_nonneg hs0 _) (by linarith)
      have h4 : s ^ (W + 1 + 1) = s ^ (W + 1) * s := pow_succ s (W + 1)
      nlinarith [h3, h4]
  have hsumC : ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) ≤
      ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hCcard j (Finset.mem_range.mp hj)) (Nat.cast_nonneg _)
  have e1 : ∑ j ∈ Finset.range V, (S : ℝ) * (d * s ^ (j + 1)) =
      ((S : ℝ) * d) * ∑ j ∈ Finset.range V, s ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSd : (0 : ℝ) ≤ (S : ℝ) * d := by positivity
  have hg2 : ∑ j ∈ Finset.range V, s ^ (j + 1) ≤ 2 * s := by
    have h5 := hgeom V
    have h6 := pow_nonneg hs0 (V + 1)
    linarith
  have hfin := mul_le_mul_of_nonneg_left hg2 hSd
  have hcast : (ℓ : ℝ) ≤ (τ : ℝ) * d + ∑ j ∈ Finset.range V, (S : ℝ) * ((C j).card : ℝ) := by
    have h7 : ((ℓ : ℕ) : ℝ) ≤ ((τ * d + ∑ j ∈ Finset.range V, S * (C j).card : ℕ) : ℝ) := by
      exact_mod_cast hℓT
    push_cast at h7
    exact h7
  nlinarith [hcast, hsumC, e1, hfin]

end CyclicSpanLengthLemmas

end Formalism.G0
