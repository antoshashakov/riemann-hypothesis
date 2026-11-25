module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpace
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  exact GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace
