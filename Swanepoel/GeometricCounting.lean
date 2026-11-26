module
public import Swanepoel.RhombusEnumeration
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem ordered_edge_count {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((Finset.univ.product Finset.univ).filter
      (fun p : Fin n × Fin n => p.1<p.2 ∧ G.Adj p.1 p.2)).card=G.edgeFinset.card := by
  classical
  refine Finset.card_bij (fun p _ => s(p.1,p.2)) ?_ ?_ ?_
  · intro p hp
    exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hp).2.2
  · intro p hp q hq he
    have hpl := (Finset.mem_filter.mp hp).2.1
    have hql := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext h.1 h.2
    · have h1 := h.1
      have h2 := h.2
      rw [h1,h2] at hpl
      exact False.elim (not_lt_of_ge (le_of_lt hql) hpl)
  · intro z
    refine Sym2.inductionOn z ?_
    intro i j hij
    have ha : G.Adj i j := SimpleGraph.mem_edgeFinset.mp hij
    rcases lt_or_gt_of_ne ha.ne with h | h
    · refine ⟨(i,j),?_,rfl⟩
      simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,true_and]
      exact ⟨h,ha⟩
    · refine ⟨(j,i),?_,?_⟩
      · simp only [Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_univ,true_and]
        exact ⟨h,ha.symm⟩
      · exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)

theorem TrackSystem.q_eq_edgeCount (D : TrackSystem) :
    D.q=D.crossing.edgeFinset.card := ordered_edge_count D.crossing

theorem componentSystem_q_eq_rhombi {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (ordinary : Finset (TrackComponent G)) (defects : ℕ) :
    (componentSystem G ht ordinary defects).q=Fintype.card (RhombusSet G) := by
  rw [TrackSystem.q_eq_edgeCount]
  have he := (SimpleGraph.Iso.comap (Fintype.equivFin (TrackComponent G)).symm
    (componentGraph G ht)).card_edgeFinset_eq
  have hr := rhombus_count_eq_crossings G ht
  have hc : (componentSystem G ht ordinary defects).crossing.edgeFinset.card=
      (componentGraph G ht).edgeFinset.card := by
    change ((componentGraph G ht).comap (Fintype.equivFin (TrackComponent G)).symm).edgeFinset.card=
      (componentGraph G ht).edgeFinset.card
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using he
  exact hc.trans hr.symm

end Swanepoel
