module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
public import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

@[expose] public section

namespace IsRegularLocalRing

open IsLocalRing

universe u

private theorem spanFinrank_span_finset_le_card {R : Type*} [CommRing R] (s : Finset R) :
    Submodule.spanFinrank (Ideal.span (s : Set R)) ≤ s.card := by
  have h2 : (Ideal.span (s : Set R)).FG := Submodule.fg_span s.finite_toSet
  have h1 : (Ideal.span (s : Set R)).spanRank ≤ Cardinal.mk ((s : Set R)) :=
    Submodule.spanRank_span_le_card _
  rw [Submodule.FG.spanRank_eq_spanFinrank h2] at h1
  have h3 : Cardinal.mk ((s : Set R)) = (s.card : Cardinal) := by simp
  rw [h3] at h1
  exact_mod_cast h1

private theorem exists_repr_ne_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ j, b.repr v j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : b.repr v = 0 := by
    ext j
    simp [h j]
  apply hv
  have h1 := congrArg (b.repr.symm) h0
  simpa using h1

private theorem span_insert_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (v : V) {j : Fin N}
    (hj : b.repr v j ≠ 0) :
    Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) = ⊤ := by
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [SetLike.mem_coe]
  by_cases hij : i = j
  · rw [hij]
    have hmem1 : v ∈ Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hmem2 : ∑ l ∈ Finset.univ.erase j, b.repr v l • b l ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, Finset.mem_coe.mpr hl, rfl⟩)
    have hsub : v - ∑ l ∈ Finset.univ.erase j, b.repr v l • b l = b.repr v j • b j := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), b.sum_repr v]
      abel
    have hkey : b.repr v j • b j ∈
        Submodule.span K (insert v (⇑b '' ↑(Finset.univ.erase j))) := by
      rw [← hsub]
      exact Submodule.sub_mem _ hmem1 hmem2
    have h2 := Submodule.smul_mem _ (b.repr v j)⁻¹ hkey
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h2
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, by simp [hij], rfl⟩)

private theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hIne : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0 := by
    intro h
    have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hIne ((Ideal.eq_top_iff_one _).mpr h1)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem spanFinrank_maximalIdeal_quotient_add_one_le_finrank (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) + 1 ≤
      Module.finrank (ResidueField R) (CotangentSpace R) :=
  ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2

private theorem eq_natCast_and_add_one_eq_of_le {a : WithBot ℕ∞} {d n : ℕ}
    (h1 : ((n : ℕ) : WithBot ℕ∞) ≤ a + 1) (h2 : a ≤ ((d : ℕ) : WithBot ℕ∞)) (h3 : d + 1 ≤ n) :
    a = ((d : ℕ) : WithBot ℕ∞) ∧ a + 1 = ((n : ℕ) : WithBot ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a = ((m : ℕ) : WithBot ℕ∞) := by
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      rw [WithBot.bot_add, le_bot_iff] at h1
      exact WithBot.natCast_ne_bot n h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h2' : (⊤ : ℕ∞) ≤ (d : ℕ∞) := by exact_mod_cast h2
        simp at h2'
      | coe m => exact ⟨m, by norm_cast⟩
  have hmd : m ≤ d := by exact_mod_cast h2
  have hnm : n ≤ m + 1 := by exact_mod_cast h1
  have hm : m = d := by omega
  have hn : n = m + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [hm]
  · rw [hn]
    norm_cast

private theorem spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq (R : Type*) [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ Ideal.span ({x} : Set R))] :
    ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) : WithBot ℕ∞)
        = ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have hdn := spanFinrank_maximalIdeal_quotient_add_one_le_finrank R hx hx2
  have hRdim : ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞)
      = ringKrullDim R := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal
  have hdimQuot : ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) ≤
      ((Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) : ℕ) :
        WithBot ℕ∞) := by
    exact_mod_cast ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span ({x} : Set R))
  have hIj : Ideal.span ({x} : Set R) ≤ Ring.jacobson R := by
    refine le_trans ?_ (IsLocalRing.ringJacobson_eq_maximalIdeal R).ge
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hdimLe := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
      (Ideal.span ({x} : Set R)) hIj
  have h1 : Submodule.spanFinrank (Ideal.span ({x} : Set R)) ≤ 1 := by
    have h := spanFinrank_span_finset_le_card ({x} : Finset R)
    simpa using h
  have hcast : ((Submodule.spanFinrank (Ideal.span ({x} : Set R)) : ℕ) : WithBot ℕ∞) ≤ 1 := by
    exact_mod_cast h1
  have hdimSucc : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 :=
    hdimLe.trans (add_le_add le_rfl hcast)
  obtain ⟨hA, hB⟩ := eq_natCast_and_add_one_eq_of_le
    (d := Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))))
    (n := Module.finrank (ResidueField R) (CotangentSpace R))
    (by rw [hRdim]; exact hdimSucc) hdimQuot hdn
  refine ⟨hA.symm, ?_⟩
  rw [hB, hRdim]

private theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1

private theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle

private theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hp : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R

private theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R
  rw [← pow_two]
  exact h

private theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2
    · obtain ⟨p, hp, hyp⟩ := hcon y hy hm2
      have hpt : p ∈ insert (maximalIdeal R ^ 2) t := by
        apply Finset.mem_insert_of_mem
        rw [← Finset.mem_coe, ht]
        exact hp
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by
      rcases Finset.mem_insert.mp hi with hh | hh
      · exact absurd hh h1
      · exact hh
    refine isPrime_of_mem_minimalPrimes ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with hh | hh
  · subst hh
    exact hsq hle
  · refine hmin ⟨i, ?_, hle⟩
    rw [← ht]
    exact Finset.mem_coe.mpr hh

theorem isRegularLocalRing_quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_ringKrullDim_and_add_one_eq R hx hx2).2

private theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R :=
  ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain_of_forall_spanFinrank_lt R IH

private theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact IH S (by omega)

theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

private theorem false_of_eq_smul_of_linearIndependent {K M : Type*} {ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0 := by
    rw [Finset.sum_pair hij]
    simp [Ne.symm hij, he]
  have h2 := linearIndependent_iff'.mp h {i, j}
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)
  simp [Ne.symm hij] at h2

private theorem toCotangent_mul_eq_smul {R : Type*} [CommRing R] [IsLocalRing R] (r a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hra : r * a ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R).toCotangent ⟨r * a, hra⟩ : IsLocalRing.CotangentSpace R) =
      algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩ : IsLocalRing.CotangentSpace R) := by
  have h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R)
      = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R) := Subtype.ext rfl
  rw [algebraMap_smul, h1, map_smul]

theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : x i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  have h0 : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
      IsLocalRing.CotangentSpace R) = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    exact hmem
  exact hli.ne_zero i h0

theorem isPrime_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : (Ideal.span ({x i} : Set R)).IsPrime := by
  have : IsRegularLocalRing (R ⧸ Ideal.span ({x i} : Set R)) :=
    isRegularLocalRing_quotient_span_singleton (hx i) (notMem_maximalIdeal_sq x hx hli i)
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact IsRegularLocalRing.isDomain _

theorem notMem_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R := by
    rw [hr]
    exact hx j
  have key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ :
      IsLocalRing.CotangentSpace R)
      = algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
          IsLocalRing.CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩ :=
      Subtype.ext hr.symm
    rw [hsub]
    exact toCotangent_mul_eq_smul r (x i) (hx i) hmem2
  exact false_of_eq_smul_of_linearIndependent hli hij _ key

theorem isRadical_span_singleton_prod {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)

end IsRegularLocalRing
