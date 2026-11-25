module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ImportsAlt
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters

open Matrix

theorem isIrreducible_iff {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeExistence.main
  | exact _root_.GlobalTheory.UnimodularLatticeExistence.main
  | (apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeExistence.main ..)

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
