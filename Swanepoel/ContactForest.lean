module
public import Swanepoel.ContactGraph
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem finite_forest_exists_leaf {V : Type*} [Fintype V] (H : SimpleGraph V)
    (ha : H.IsAcyclic) {a b : V} (hab : H.Adj a b) :
    ∃ v w : V, H.Adj v w ∧ ∀ z, H.Adj v z → z=w := by
  classical
  let C := H.connectedComponentMk a
  have haC : a ∈ C := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hbC : b ∈ C := C.mem_supp_of_adj_mem_supp haC hab
  let : Fintype C := Fintype.ofFinite C
  let : Nontrivial C := ⟨⟨⟨a,haC⟩,⟨b,hbC⟩,fun he => hab.ne (congrArg Subtype.val he)⟩⟩
  have htree : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,ha.induce C.supp⟩
  obtain ⟨v,hv⟩ := htree.exists_vert_degree_one_of_nontrivial
  obtain ⟨w,hadj,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  refine ⟨v.val,w.val,hadj,?_⟩
  intro z hvz
  have hzC : z ∈ C := C.mem_supp_of_adj_mem_supp v.property hvz
  exact congrArg Subtype.val (hunique ⟨z,hzC⟩ hvz)

theorem PennyGraph.contact_forest_leaf {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (ha : (G.contactGraph S).IsAcyclic)
    (hS : S.Nonempty) :
    ∃ e ∈ S,
      (∀ f ∈ S.erase e, f.val.1≠e.val.1 ∧ f.val.2≠e.val.1) ∨
      (∀ f ∈ S.erase e, f.val.1≠e.val.2 ∧ f.val.2≠e.val.2) := by
  classical
  obtain ⟨e,he⟩ := hS
  obtain ⟨v,w,hvw,hu⟩ := finite_forest_exists_leaf (G.contactGraph S) ha
    ((G.contactGraph_adj_iff S e).mpr he)
  obtain ⟨e,he,hev⟩ := hvw
  have heq (f : ContactEdge G) (hf : f∈S)
      (hvf : f.val.1=v ∨ f.val.2=v) : f=e := by
    have hfadj := (G.contactGraph_adj_iff S f).mpr hf
    have hpair : s(f.val.1,f.val.2)=s(v,w) := by
      rcases hvf with h | h
      · have hother := hu f.val.2 (h ▸ hfadj)
        rw [h,hother]
      · have hother := hu f.val.1 (h ▸ hfadj.symm)
        rw [h,hother]
        exact Sym2.eq_swap
    exact f.eq_of_unordered_eq e (hpair.trans hev.symm)
  refine ⟨e,he,?_⟩
  rcases Sym2.eq_iff.mp hev with h | h
  · left
    intro f hf
    have hfS := (Finset.mem_erase.mp hf).2
    have hfe := (Finset.mem_erase.mp hf).1
    constructor
    · intro hh
      exact hfe (heq f hfS (Or.inl (hh.trans h.1)))
    · intro hh
      exact hfe (heq f hfS (Or.inr (hh.trans h.1)))
  · right
    intro f hf
    have hfS := (Finset.mem_erase.mp hf).2
    have hfe := (Finset.mem_erase.mp hf).1
    constructor
    · intro hh
      exact hfe (heq f hfS (Or.inl (hh.trans h.2)))
    · intro hh
      exact hfe (heq f hfS (Or.inr (hh.trans h.2)))

end Swanepoel
