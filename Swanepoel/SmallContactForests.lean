module
public import Swanepoel.EulerForest
public import Mathlib.Combinatorics.SimpleGraph.Clique
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem triangle_free_cycle_four_le {V : Type*} (H : SimpleGraph V)
    (ht : ∀ a b c, H.Adj a b → H.Adj b c → ¬H.Adj c a)
    {a : V} (p : H.Walk a a) (hp : p.IsCycle) : 4≤p.length := by
  classical
  by_contra hn
  have hlen : p.length=3 := by have := hp.three_le_length; omega
  obtain ⟨S,hS⟩ := H.is3Clique_iff_exists_cycle_length_three.mpr ⟨a,p,hp,hlen⟩
  obtain ⟨u,v,w,huv,huw,hvw,_⟩ := SimpleGraph.is3Clique_iff.mp hS
  exact ht u v w huv hvw huw.symm

theorem cycle_length_le_edge_count {V : Type*} [Fintype V] (H : SimpleGraph V)
    {a : V} (p : H.Walk a a) (hp : p.IsCycle) : p.length≤H.edgeFinset.card := by
  classical
  calc
    p.length=p.edges.toFinset.card := by
      rw [List.toFinset_card_of_nodup hp.edges_nodup,p.length_edges]
    _ ≤ H.edgeFinset.card := Finset.card_le_card (by
      intro z hz
      exact SimpleGraph.mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp hz)))

theorem triangle_free_isAcyclic_of_edge_count_le_three {V : Type*} [Fintype V]
    (H : SimpleGraph V)
    (ht : ∀ a b c, H.Adj a b → H.Adj b c → ¬H.Adj c a)
    (hm : H.edgeFinset.card≤3) : H.IsAcyclic := by
  intro a p hp
  have hlow := triangle_free_cycle_four_le H ht p hp
  have hhigh := cycle_length_le_edge_count H p hp
  omega

theorem PennyGraph.small_contact_isAcyclic {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (S : Finset (ContactEdge G)) (hS : S.card≤3) :
    (G.contactGraph S).IsAcyclic := by
  apply triangle_free_isAcyclic_of_edge_count_le_three (G.contactGraph S)
  · intro a b c hab hbc hca
    exact ht a b c (G.contactGraph_le S hab) (G.contactGraph_le S hbc)
      (G.contactGraph_le S hca)
  · rwa [G.contactGraph_edge_count]

theorem PennyGraph.IsSubFace.not_isBounded_of_acyclic {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F)
    (ha : (G.contactGraph S).IsAcyclic) : ¬Bornology.IsBounded F := by
  obtain ⟨x,hx,rfl⟩ := hf
  rw [(G.subdrawing_complement_connected_of_acyclic S ha).isPreconnected.connectedComponentIn hx]
  intro hb
  have hwhole := (G.isCompact_subdrawing S).isBounded.union hb
  rw [Set.union_compl_self] at hwhole
  exact NormedSpace.unbounded_univ ℝ Plane hwhole

theorem PennyGraph.IsSubFace.not_isBounded_of_card_le_three {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F)
    (ht : G.TriangleFree) (hS : S.card≤3) : ¬Bornology.IsBounded F :=
  hf.not_isBounded_of_acyclic (G.small_contact_isAcyclic ht S hS)

theorem PennyGraph.IsSubFace.four_le_selected_edges {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F)
    (ht : G.TriangleFree) (hb : Bornology.IsBounded F) : 4≤S.card := by
  by_contra hn
  exact hf.not_isBounded_of_card_le_three ht (by omega) hb

end Swanepoel
