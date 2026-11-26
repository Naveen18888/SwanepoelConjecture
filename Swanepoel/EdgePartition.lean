module
public import Swanepoel.Restrictions
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem induced_edge_partition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) (hcover : S ∪ T = Finset.univ)
    (hoverlap : ∀ u ∈ S, u ∈ T → ∀ v ∈ S, v ∈ T → u = v)
    (hsep : ∀ u ∈ S, u ∉ T → ∀ v ∈ T, v ∉ S → ¬ G.Adj u v) :
    G.edgeFinset.card = (G.induce (↑S : Set V)).edgeFinset.card +
      (G.induce (↑T : Set V)).edgeFinset.card := by
  classical
  have hverts (v : V) : v ∈ S ∨ v ∈ T := by
    rw [← Finset.mem_union, hcover]
    exact Finset.mem_univ _
  have hp (u v : V) (huv : G.Adj u v) :
      (u ∈ T ∧ v ∈ T) ↔ ¬ (u ∈ S ∧ v ∈ S) := by
    constructor
    · rintro ⟨huT, hvT⟩ ⟨huS, hvS⟩
      exact huv.ne (hoverlap u huS huT v hvS hvT)
    · intro hn
      by_cases huT : u ∈ T
      · refine ⟨huT, ?_⟩
        by_contra hvT
        have hvS := (hverts v).resolve_right hvT
        have huS : u ∉ S := fun huS => hn ⟨huS, hvS⟩
        exact hsep v hvS hvT u huT huS huv.symm
      · have huS := (hverts u).resolve_right huT
        have hvS : v ∉ S := fun hvS => hn ⟨huS, hvS⟩
        have hvT := (hverts v).resolve_left hvS
        exact False.elim (hsep u huS huT v hvT hvS huv)
  have hf : G.edgeFinset.filter (fun e => e.toFinset ⊆ T) =
      G.edgeFinset.filter (fun e => ¬ e.toFinset ⊆ S) := by
    apply Finset.filter_congr
    intro e
    refine Sym2.inductionOn e ?_
    intro u v he
    have huv : G.Adj u v := by simpa using he
    simpa only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using hp u v huv
  rw [← G.card_filter_edgeFinset_toFinset_subset S,
    ← G.card_filter_edgeFinset_toFinset_subset T, hf]
  exact (Finset.card_filter_add_card_filter_not _).symm

end Swanepoel
