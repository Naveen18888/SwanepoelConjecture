module
public import Swanepoel.BoundarySpokeClosing
public import Swanepoel.NilSpokeBanks
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem PositiveSpineChain.spoke_closing_loop_support {n : ℕ} {G : PennyGraph n}
    {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (cut : TrackComponent G) (F outer : PlaneFace G)
    (close : PlaneChain (edgeCenter t) (edgeCenter s))
    (hclose : G.SpokeClosingSupport cut F outer s t close) :
    G.SpokePairSupport (edgeComponent s) cut F outer (p.toPlane.append close) := by
  have hs : edgeCenter s∈trackSpineTrace (edgeComponent s) := Or.inl ⟨s,rfl,rfl⟩
  have ht : edgeCenter t∈trackSpineTrace (edgeComponent s) :=
    Or.inl ⟨t,(positive_path_component p.reach).symm,rfl⟩
  dsimp only [PennyGraph.SpokePairSupport]
  rw [PlaneChain.trace_append]
  refine Set.union_subset (fun _ hz => Or.inl (Or.inl (Or.inl (p.trace_subset_track hz)))) ?_
  intro z hz
  rcases hclose hz with ((hcut | hend) | hF) | hO
  · exact Or.inl (Or.inl (Or.inr hcut))
  · rcases hend with hzs | hzt
    · exact Or.inl (Or.inl (Or.inl (hzs.symm ▸ hs)))
    · exact Or.inl (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hzt).symm ▸ ht)))
  · exact Or.inl (Or.inr hF)
  · exact Or.inr hO

theorem PositiveSpineChain.spoke_closing_bank_difference {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (cut : TrackComponent G) (hne : edgeComponent s≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent s) cut)
    (F outer : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (houter : ¬Bornology.IsBounded outer.val)
    (close : PlaneChain (edgeCenter t) (edgeCenter s))
    (hclose : G.SpokeClosingSupport cut F outer s t close)
    (hstep : ∃d,PositiveCellStep s d) :
    p.bankLabel (p.toPlane.append close) (-1)=p.bankLabel (p.toPlane.append close) 1+1 := by
  have hsupport := p.spoke_closing_loop_support cut F outer close hclose
  have hdis := p.bankRegion_avoids_spoke_pair_loop ht hs htop cut hne hmiss F outer hF houter
    (p.toPlane.append close) hsupport
  cases p with
  | nil s => exact False.elim (htop hstep)
  | cons s b t h tail =>
    let p := PositiveSpineChain.cons s b t h tail
    let loop := p.toPlane.append close
    have hmclose : stepCenter s b∉close.trace :=
      h.midpoint_not_spoke_closing ht rfl cut hne hmiss F outer hF houter close hclose
    have hmtail : stepCenter s b∉tail.toPlane.trace := by
      intro hz
      have hh := (tail.height_bounds hz).1
      rw [← h.to_cellStep.vector_eq] at hh
      linarith [h.midpoint_height_between.2]
    have hm : (1/2:ℝ) • (edgeCenter s+edgeCenter b)∉(tail.toPlane.append close).trace := by
      rw [PlaneChain.trace_append]
      exact fun hz => hz.elim hmtail hmclose
    have hneMid : edgeCenter s≠edgeCenter b := by
      intro heq
      have hh : edgeHeight s=edgeHeight b := by
        unfold edgeHeight
        rw [h.to_cellStep.vector_eq,heq]
      exact (ne_of_lt h.height_lt) hh
    obtain ⟨ε,hε,hjump⟩ := PlaneChain.segment_loop_winding_jump hneMid (tail.toPlane.append close) hm
    have hloop : loop=(PlaneChain.single (edgeCenter s) (edgeCenter b)).append (tail.toPlane.append close) := rfl
    apply p.bankLabel_difference_of_disjoint ht loop hdis Relation.ReflTransGen.refl
      (show segment ℝ (edgeCenter s) (edgeCenter b)⊆p.toPlane.trace from Set.subset_union_left) h ε hε
    intro r hr hre
    rw [hloop]
    exact (hjump r hr hre).2.2.1

theorem PennyGraph.boundary_spoke_pair_banks {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F)
    (hne : edgeComponent e≠edgeComponent f) (hmiss : ¬ComponentCrosses (edgeComponent e) (edgeComponent f)) :
    ∃ t : OrientedEdge G, ∃ p : PositiveSpineChain G e t,
      (¬∃g,PositiveCellStep t g) ∧
      ∃ loop : PlaneChain (edgeCenter e) (edgeCenter e),
        G.SpokePairSupport (edgeComponent e) (edgeComponent f) F outer loop ∧
        trackSpineTrace (edgeComponent e)⊆loop.trace ∧ trackSpineTrace (edgeComponent f)⊆loop.trace ∧
        (∀ sign : ℝ,sign=1 ∨ sign= -1 → Disjoint (p.bankRegion sign) loop.trace) ∧
        ((∃d,PositiveCellStep e d) → p.bankLabel loop (-1)=p.bankLabel loop 1+1) := by
  obtain ⟨t,htop,hreach,htF⟩ := G.boundary_port_complete_spine_to_outer ht hY F hFY hports outer houter e he
  obtain ⟨p⟩ := PositiveSpineChain.exists_of_reach hreach
  obtain ⟨close,hclose,hfullF⟩ := G.boundary_spoke_closing_route ht hY F hFY hports outer houter e f he hf t htF
  let loop := p.toPlane.append close
  have hs : SpineSource e := (Finset.mem_filter.mp he).2.1
  have hsupport := p.spoke_closing_loop_support (edgeComponent f) F outer close hclose
  have hcloseSub : close.trace⊆loop.trace := by
    change close.trace⊆(p.toPlane.append close).trace
    rw [PlaneChain.trace_append]
    exact Set.subset_union_right
  refine ⟨t,p,htop,loop,hsupport,?_,hfullF.trans hcloseSub,?_,?_⟩
  · rw [← p.complete_trace ht hs htop]
    change p.toPlane.trace⊆(p.toPlane.append close).trace
    rw [PlaneChain.trace_append]
    exact Set.subset_union_left
  · exact p.bankRegion_avoids_spoke_pair_loop ht hs htop _ hne hmiss F outer (hY.subset_defects hFY)
      houter loop hsupport
  · exact p.spoke_closing_bank_difference ht hs htop _ hne hmiss F outer (hY.subset_defects hFY)
      houter close hclose

theorem PennyGraph.boundary_spoke_pair_banks_full {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F)
    (hne : edgeComponent e≠edgeComponent f) (hmiss : ¬ComponentCrosses (edgeComponent e) (edgeComponent f)) :
    ∃ t : OrientedEdge G, ∃ p : PositiveSpineChain G e t,
      (¬∃g,PositiveCellStep t g) ∧
      ∃ loop : PlaneChain (edgeCenter e) (edgeCenter e),
        G.SpokePairSupport (edgeComponent e) (edgeComponent f) F outer loop ∧
        trackSpineTrace (edgeComponent e)⊆loop.trace ∧ trackSpineTrace (edgeComponent f)⊆loop.trace ∧
        (∀ sign : ℝ,sign=1 ∨ sign= -1 → Disjoint (p.bankRegion sign) loop.trace) ∧
        p.bankLabel loop (-1)=p.bankLabel loop 1+1 := by
  by_cases hstep : ∃ d,PositiveCellStep e d
  · obtain ⟨t,p,htop,loop,hsupport,hfirst,hsecond,hdis,hdiff⟩ :=
      G.boundary_spoke_pair_banks ht hY F hFY hports outer houter e f he hf hne hmiss
    exact ⟨t,p,htop,loop,hsupport,hfirst,hsecond,hdis,hdiff hstep⟩
  · obtain ⟨t,_,hreach,htF⟩ := G.boundary_port_complete_spine_to_outer ht hY F hFY hports outer houter e he
    have het : e=t := by
      rcases hreach.cases_head with h | ⟨b,heb,_⟩
      · exact h
      · exact False.elim (hstep ⟨b,heb⟩)
    subst t
    obtain ⟨loop,hsupport,hfirst,hsecond,hdis,hdiff⟩ :=
      G.boundary_nil_spoke_pair_banks ht hY F hFY hports outer houter e f he hf hne hmiss hstep htF
    exact ⟨e,.nil e,hstep,loop,hsupport,hfirst,hsecond,hdis,hdiff⟩

end Swanepoel
