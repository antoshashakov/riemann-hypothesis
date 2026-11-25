module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open ValuativeRel Matrix Topology MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.IwContract

open PositivityTheory.Rg.Tf.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ↔ g ∈ GlobalTheory.SmGL.iwahori F (Fin n) := by
  rw [GlobalTheory.SmGL.mem_iwahori]; rfl


end GlobalTheory.CompanionTheory.IwContract
