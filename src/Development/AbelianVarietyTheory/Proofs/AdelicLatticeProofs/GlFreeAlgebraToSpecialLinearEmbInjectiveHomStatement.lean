module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHom
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  first | exact @GlobalTheory.ClassFin.EmbHom.emb_hom | exact GlobalTheory.ClassFin.EmbHom.emb_hom | (intros; apply GlobalTheory.ClassFin.EmbHom.emb_hom <;> assumption)
