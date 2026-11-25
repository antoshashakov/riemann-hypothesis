module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceSupSpanSqLeAdd
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem homRange {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {ι : Type} (t : ι → A) (d : ℤ) (ht : ∀ i, t i ∈ 𝒜 d) :
    (Ideal.span (Set.range t)).IsHomogeneous 𝒜 := by
  refine Ideal.homogeneous_span 𝒜 _ ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨d, ht i⟩

private theorem sqMem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {t : A} {d : ℤ} (ht : t ∈ 𝒜 d) : t ^ 2 ∈ 𝒜 (d + d) := by
  rw [pow_two]
  exact SetLike.mul_mem_graded ht ht

private theorem spanSucc {A : Type} [CommRing A] {n : ℕ} (t : Fin (n + 1) → A) :
    Ideal.span (Set.range t) = Ideal.span {t 0} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) := by
  rw [Fin.range_fin_succ, Ideal.span_insert]
  rfl

private theorem gen {O K A : Type} [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (σ : 𝒜 0 →ₐ[O] K) (d : ℤ) (c : ℕ∞) (n : ℕ) :
    ∀ (t : Fin n → A), (∀ i, t i ∈ 𝒜 d) → ∀ J : Ideal A, J.IsHomogeneous 𝒜 →
      (∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range t)) w) ≤ c) →
      ∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range fun i => t i ^ 2)) w) ≤ 2 ^ n * c := by
  induction n generalizing c with
  | zero =>
    intro t _ J _ h w
    have e1 : Set.range (fun i : Fin 0 => t i ^ 2) = Set.range t := by
      simp [Set.range_eq_empty]
    rw [e1, pow_zero, one_mul]
    exact h w
  | succ n ih =>
    intro t ht J hJ h w
    have hJ1 : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)).IsHomogeneous 𝒜 :=
      hJ.sup (homRange 𝒜 _ d fun i => ht i.succ)
    have h1 : ∀ w', locLen σ (aPiece 𝒜 ((J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔
        Ideal.span {t 0 ^ 2}) w') ≤ 2 * c := by
      intro w'
      have e : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0} =
          J ⊔ Ideal.span (Set.range t) := by
        rw [spanSucc t, sup_assoc, sup_comm (Ideal.span (Set.range fun i : Fin n => t i.succ))]
      refine (locLen_aPiece_sup_span_sq_le_add O K A 𝒜 σ _ hJ1 d (t 0) (ht 0) w').trans ?_
      rw [e, two_mul]
      exact add_le_add (h _) (h _)
    have hsq : (Ideal.span ({t 0 ^ 2} : Set A)).IsHomogeneous 𝒜 := by
      apply Ideal.homogeneous_span
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨d + d, sqMem 𝒜 (ht 0)⟩
    have hJ2 : (J ⊔ Ideal.span {t 0 ^ 2}).IsHomogeneous 𝒜 := hJ.sup hsq
    have h2 := ih (2 * c) (fun i => t i.succ) (fun i => ht i.succ) (J ⊔ Ideal.span {t 0 ^ 2}) hJ2
      (by
        intro w'
        have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) =
            (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0 ^ 2} := by
          rw [sup_assoc, sup_assoc, sup_comm (Ideal.span {t 0 ^ 2})]
        rw [e]
        exact h1 w') w
    have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ ^ 2) =
        J ⊔ Ideal.span (Set.range fun i => t i ^ 2) := by
      rw [spanSucc (fun i => t i ^ 2), sup_assoc]
    rw [e] at h2
    calc _ ≤ 2 ^ n * (2 * c) := h2
      _ = 2 ^ (n + 1) * c := by rw [pow_succ, mul_assoc]

theorem UpperTheory.V.Alg.M.locLen_aPiece_ideal2_le_two_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, (∀ w, locLen σ (aPiece 𝒜 Q.ideal w) ≤ 1) → ∀ w, locLen σ (aPiece 𝒜 (ideal2 Q) w) ≤ 2 ^ (r + 1 + r') := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q σ hOne w
  let J := Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z)
  have hJ : J.IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro y ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨-2, Q.hG i⟩
    · exact ⟨2, Q.hE' i⟩
    · exact ⟨0, (Q.hZ i).1⟩
  let E := Ideal.span (Set.range Q.E)
  let F₂ := Ideal.span (Set.range fun i => Q.F i ^ 2)
  let E₂ := Ideal.span (Set.range fun i => Q.E i ^ 2)
  have hOriginal : J ⊔ E ⊔ Ideal.span (Set.range Q.F) = Q.ideal := by
    simp only [J, E, Eqns.ideal, Ideal.span_union]; ac_rfl
  have hSquared : J ⊔ F₂ ⊔ E₂ = ideal2 Q := by
    simp only [J, F₂, E₂, ideal2, Ideal.span_union]; ac_rfl
  have bound (L : ℕ∞) (h : ∀ v, locLen σ (aPiece 𝒜 Q.ideal v) ≤ L) :
      locLen σ (aPiece 𝒜 (ideal2 Q) w) ≤ 2 ^ (r + 1 + r') * L := by
    have hF := gen 𝒜 σ (-1) L (r + 1) Q.F Q.hF (J ⊔ E)
      (hJ.sup (homRange 𝒜 Q.E 1 Q.hE)) (by rw [hOriginal]; exact h)
    have hE := gen 𝒜 σ 1 (2 ^ (r + 1) * L) r' Q.E Q.hE
      (J ⊔ F₂) (hJ.sup (homRange 𝒜 _ (-1 + -1) fun i => sqMem 𝒜 (Q.hF i))) (by
        change ∀ v, locLen σ (aPiece 𝒜 (J ⊔ F₂ ⊔ E) v) ≤ _
        rw [show J ⊔ F₂ ⊔ E = J ⊔ E ⊔ F₂ by ac_rfl]; exact hF) w
    change locLen σ (aPiece 𝒜 (J ⊔ F₂ ⊔ E₂) w) ≤ _ at hE
    rw [hSquared] at hE
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hE
  simpa only [mul_one] using bound 1 hOne
