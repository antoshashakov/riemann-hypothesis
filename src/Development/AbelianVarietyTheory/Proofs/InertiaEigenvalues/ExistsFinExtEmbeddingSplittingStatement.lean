module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.exists_finExt_embedding_splitting' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  first | exact @GlobalTheory.exists_finExt_embedding_splitting | exact GlobalTheory.exists_finExt_embedding_splitting | (intros; apply GlobalTheory.exists_finExt_embedding_splitting <;> assumption)
