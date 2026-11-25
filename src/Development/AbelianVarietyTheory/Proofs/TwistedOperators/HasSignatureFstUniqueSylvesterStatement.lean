module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.hasSignature_fst_unique_sylvester : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ}, Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' := by
  first | exact @GlobalTheory.SylvesterInertia.hasSignature_fst_unique | exact GlobalTheory.SylvesterInertia.hasSignature_fst_unique | (intros; apply GlobalTheory.SylvesterInertia.hasSignature_fst_unique <;> assumption)
