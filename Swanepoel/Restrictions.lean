module
public import Swanepoel.Gluing
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PennyGraph

def restrict {n : ℕ} (G : PennyGraph n) (S : Finset (Fin n)) : PennyGraph S.card where
  point i := G.point ((S.equivFin).symm i)
  separated i j hij := G.separated _ _ (by
    intro he
    apply hij
    exact (S.equivFin).symm.injective (Subtype.ext he))

def restrictIso {n : ℕ} (G : PennyGraph n) (S : Finset (Fin n)) :
    (G.restrict S).graph ≃g G.graph.induce (↑S : Set (Fin n)) where
  toEquiv := S.equivFin.symm
  map_rel_iff' := by
    intro i j
    change ((S.equivFin.symm i).val ≠ (S.equivFin.symm j).val ∧ _) ↔ (i ≠ j ∧ _)
    have he : (S.equivFin.symm i).val = (S.equivFin.symm j).val ↔ i = j :=
      ⟨fun h => S.equivFin.symm.injective (Subtype.ext h),
        fun h => congrArg (fun k => (S.equivFin.symm k).val) h⟩
    simp only [ne_eq, he]
    rfl

theorem restrict_triangleFree {n : ℕ} (G : PennyGraph n) (S : Finset (Fin n))
    (hG : G.TriangleFree) : (G.restrict S).TriangleFree := by
  intro a b c hab hbc hca
  exact hG _ _ _ ((G.restrictIso S).map_rel_iff.mpr hab)
    ((G.restrictIso S).map_rel_iff.mpr hbc) ((G.restrictIso S).map_rel_iff.mpr hca)

theorem restrict_edgeCount {n : ℕ} (G : PennyGraph n) (S : Finset (Fin n)) :
    (G.restrict S).edgeCount = (G.graph.induce (↑S : Set (Fin n))).edgeFinset.card :=
  (G.restrictIso S).card_edgeFinset_eq

end PennyGraph

theorem small_graph_upper_bound {n : ℕ} (G : PennyGraph n) (hn : 1 ≤ n) (hsmall : n ≤ 2) :
    (G.edgeCount : ℤ) ≤ extremalValue n := by
  have hm : G.edgeCount ≤ n.choose 2 := by
    simpa [PennyGraph.edgeCount] using G.graph.card_edgeFinset_le_card_choose_two
  have hcases : n = 1 ∨ n = 2 := by omega
  rcases hcases with h | h
  · subst n
    norm_num [extremalValue] at *
    omega
  · subst n
    norm_num at hm
    have hF : (1 : ℤ) ≤ extremalValue 2 := by
      unfold extremalValue
      apply Int.le_floor.mpr
      norm_num only [Nat.cast_ofNat, Int.cast_one]
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hsn := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    omega

theorem finite_graph_separation {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hG : ¬ G.Connected) :
    ∃ S : Finset V, S.Nonempty ∧ (Finset.univ \ S).Nonempty ∧
      ∀ u ∈ S, ∀ v ∉ S, ¬ G.Adj u v := by
  classical
  have hp : ¬ G.Preconnected := fun h => hG { preconnected := h }
  change ¬ (∀ u v, G.Reachable u v) at hp
  simp only [not_forall] at hp
  obtain ⟨u, v, huv⟩ := hp
  refine ⟨Finset.univ.filter (G.Reachable u), ?_, ?_, ?_⟩
  · exact ⟨u, by simp⟩
  · exact ⟨v, by simp [huv]⟩
  · intro a ha b hb hab
    have hua : G.Reachable u a := (Finset.mem_filter.mp ha).2
    exact hb (by simp [hua.trans hab.reachable])

end Swanepoel
