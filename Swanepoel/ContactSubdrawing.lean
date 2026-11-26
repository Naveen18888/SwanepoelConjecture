module
public import Swanepoel.EulerPreparation
@[expose] public section

noncomputable section
namespace Swanepoel

abbrev ContactEdge {n : ℕ} (G : PennyGraph n) :=
  {p : Fin n × Fin n // p.1<p.2 ∧ G.graph.Adj p.1 p.2}

noncomputable instance {n : ℕ} (G : PennyGraph n) : Fintype (ContactEdge G) := Fintype.ofFinite _

theorem ContactEdge.eq_of_unordered_eq {n : ℕ} {G : PennyGraph n} (e f : ContactEdge G)
    (h : s(e.val.1,e.val.2)=s(f.val.1,f.val.2)) : e=f := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have he := e.property.1
    rw [h.1,h.2] at he
    exact False.elim (not_lt_of_ge (le_of_lt f.property.1) he)

def PennyGraph.subdrawing {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) : Set Plane :=
  Set.range G.point ∪ ⋃ e ∈ S, G.edgeTrace e.val.1 e.val.2

theorem PennyGraph.isCompact_subdrawing {n : ℕ} (G : PennyGraph n) (S : Finset (ContactEdge G)) :
    IsCompact (G.subdrawing S) := by
  apply (Set.finite_range G.point).isCompact.union
  exact isCompact_iUnion (fun e => isCompact_iUnion (fun _ : e∈S =>
    isCompact_Icc.image (G.continuous_edgePoint e.val.1 e.val.2)))

theorem PennyGraph.subdrawing_empty {n : ℕ} (G : PennyGraph n) :
    G.subdrawing ∅=Set.range G.point := by simp [PennyGraph.subdrawing]

theorem PennyGraph.subdrawing_insert {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) :
    G.subdrawing (insert e S)=G.subdrawing S ∪ G.edgeTrace e.val.1 e.val.2 := by
  classical
  ext z
  simp only [PennyGraph.subdrawing,Set.mem_union,Set.mem_iUnion,Finset.mem_insert]
  constructor
  · rintro (hp | ⟨f,hf,hz⟩)
    · exact Or.inl (Or.inl hp)
    · rcases hf with rfl | hf
      · exact Or.inr hz
      · exact Or.inl (Or.inr ⟨f,hf,hz⟩)
  · rintro ((hp | ⟨f,hf,hz⟩) | hz)
    · exact Or.inl hp
    · exact Or.inr ⟨f,Or.inr hf,hz⟩
    · exact Or.inr ⟨e,Or.inl rfl,hz⟩

theorem PennyGraph.subdrawing_univ {n : ℕ} (G : PennyGraph n) :
    G.subdrawing Finset.univ=G.drawing := by
  classical
  ext z
  constructor
  · rintro (hp | he)
    · exact Or.inl hp
    · obtain ⟨e,_,he⟩ := Set.mem_iUnion.mp he |>.imp (fun _ => Set.mem_iUnion.mp)
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨e.val,e.property.2⟩,he⟩)
  · rintro (hp | he)
    · exact Or.inl hp
    · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
      rcases lt_or_gt_of_ne e.property.ne with h | h
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨e.val,h,e.property⟩,
          Set.mem_iUnion.mpr ⟨Finset.mem_univ _,he⟩⟩)
      · have he' : z∈G.edgeTrace e.val.2 e.val.1 := by rwa [G.edgeTrace_reverse] at he
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨(e.val.2,e.val.1),h,e.property.symm⟩,
          Set.mem_iUnion.mpr ⟨Finset.mem_univ _,he'⟩⟩)

theorem PennyGraph.contactEdge_count {n : ℕ} (G : PennyGraph n) :
    Fintype.card (ContactEdge G)=G.edgeCount := by
  classical
  have hc : Fintype.card (ContactEdge G)=
      ((Finset.univ.product Finset.univ).filter
        (fun p : Fin n × Fin n => p.1<p.2 ∧ G.graph.Adj p.1 p.2)).card :=
    Fintype.card_of_subtype _ (by intro p; simp)
  have h := hc.trans (ordered_edge_count G.graph)
  simpa only [PennyGraph.edgeCount,SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using h

theorem PennyGraph.omitted_edge_disjoint_subdrawing {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) :
    _root_.Disjoint (G.openEdgeTrace e.val.1 e.val.2) (G.subdrawing S) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,⟨ht0,ht1⟩,rfl⟩ hdraw
  rcases hdraw with ⟨i,hi⟩ | hdraw
  · exact G.edgePoint_ne_vertex _ _ i e.property.2 ht0 ht1 hi.symm
  · obtain ⟨f,hf⟩ := Set.mem_iUnion.mp hdraw
    obtain ⟨hfS,s,⟨hs0,hs1⟩,hs⟩ := Set.mem_iUnion.mp hf
    have hp := G.interior_edge_intersection _ _ _ _ e.property.2 f.property.2 ht0 ht1 hs0 hs1 hs.symm
    have hh := e.eq_of_unordered_eq f hp
    exact he (hh ▸ hfS)

theorem PennyGraph.omitted_edge_in_one_face {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) :
    G.openEdgeTrace e.val.1 e.val.2⊆connectedComponentIn (G.subdrawing S)ᶜ
      (G.edgePoint e.val.1 e.val.2 (1/2)) := by
  have hp : G.edgePoint e.val.1 e.val.2 (1/2)∈G.openEdgeTrace e.val.1 e.val.2 :=
    ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  apply (G.isPreconnected_openEdgeTrace _ _).subset_connectedComponentIn hp
  intro z hz
  exact Set.disjoint_left.mp (G.omitted_edge_disjoint_subdrawing S e he) hz

theorem PennyGraph.omitted_edge_free_ball {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    ∃ r : ℝ, 0<r ∧ r<t ∧ r<1-t ∧
      Metric.ball (G.edgePoint e.val.1 e.val.2 t) r⊆(G.subdrawing S)ᶜ := by
  have hp : G.edgePoint e.val.1 e.val.2 t∈(G.subdrawing S)ᶜ :=
    Set.disjoint_left.mp (G.omitted_edge_disjoint_subdrawing S e he) ⟨t,⟨ht0,ht1⟩,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (G.isCompact_subdrawing S).isClosed.isOpen_compl _ hp
  let δ := min r (min t (1-t))/2
  have hpos : 0<min r (min t (1-t)) := lt_min hr (lt_min ht0 (by linarith))
  have hδr : δ<r := by have := min_le_left r (min t (1-t)); dsimp [δ]; linarith
  have hδt : δ<t := by
    have hle := (min_le_right r (min t (1-t))).trans (min_le_left t (1-t))
    dsimp [δ]; linarith
  have hδt' : δ<1-t := by
    have hle := (min_le_right r (min t (1-t))).trans (min_le_right t (1-t))
    dsimp [δ]; linarith
  exact ⟨δ,by dsimp [δ]; positivity,hδt,hδt',(Metric.ball_subset_ball hδr.le).trans hball⟩

end Swanepoel
