module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfCyclicTower
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hasseNormPrinciple_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → NP M E → NP F M → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_cyclic_tower | exact GlobalTheory.CNorm.np_of_cyclic_tower | (intros; apply GlobalTheory.CNorm.np_of_cyclic_tower <;> assumption)
