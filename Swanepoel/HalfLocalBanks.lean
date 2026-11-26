module
public import Swanepoel.HalfBankSeparation
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem MaskedSpineChain.first_midpoint_not_closing {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} {s b g h : OrientedEdge G}
    (hsb : TrackCutStep cut s b) (tail : MaskedSpineChain G cut b g)
    (hne : edgeComponent s≠cut) (C : RhombusCell G)
    (hG : g.val=(C.a,C.b)) (hH : h.val=(C.d,C.c)) (hpos : 0<cross2 C.u C.v)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (close : PlaneChain (edgeCenter g) (edgeCenter s))
    (hclose : close.trace⊆(segment ℝ (edgeCenter g) C.center∪trackSpineTrace cut)∪
      ({edgeCenter s}∪outer.val)) : stepCenter s b∉close.trace := by
  have hmid := hsb.to_positive.midpoint_height_between
  have hv : carriedVector s=carriedVector g :=
    positive_path_vector_eq (tail.positive.reach.head hsb.to_positive)
  have hbg := positive_path_height_le tail.positive.reach
  have hgh : PositiveCellStep g h := ⟨C,hG,hH,hpos⟩
  have hgeq : g=C.edgeAB := Subtype.ext hG
  have hheq : h=C.edgeDC := Subtype.ext hH
  have hcenter : C.center=stepCenter g h := by rw [hgeq,hheq,C.stepCenter_eq]
  have hcritical : ∀ z∈segment ℝ (edgeCenter g) C.center,
      edgeHeight g≤cross2 (carriedVector g) z := by
    intro z hz
    have hc : Convex ℝ {w : Plane | edgeHeight g≤cross2 (carriedVector g) w} :=
      (convex_Ici _).linear_preimage (crossLinear (carriedVector g))
    exact hc.segment_subset (by change edgeHeight g≤edgeHeight g; exact le_rfl)
      (by change edgeHeight g≤cross2 (carriedVector g) C.center
          rw [hcenter]; exact hgh.midpoint_height_between.1.le) hz
  obtain ⟨D,hS,hB,_⟩ := hsb.to_positive
  have hseq : s=D.edgeAB := Subtype.ext hS
  have hbeq : b=D.edgeDC := Subtype.ext hB
  have hm : stepCenter s b∈D.openRegion := by
    rw [hseq,hbeq,D.stepCenter_eq,← D.cellPoint_half_eq_center]
    exact D.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnotU : stepCenter s b∉trackSpineTrace cut := by
    apply Set.disjoint_left.mp (D.closedRegion_disjoint_other_spine ht cut
      (by simpa only [hseq] using hne) (hsb.other_component_ne ht D hS hB))
    exact D.openRegion_subset_closedRegion hm
  intro hz
  rcases hclose hz with (hc | hu) | (hs | ho)
  · have hh := hcritical _ hc
    rw [← hv] at hh
    linarith
  · exact hnotU hu
  · exact D.openRegion_subset_complement ht hm
      ((Set.mem_singleton_iff.mp hs).symm ▸ G.edgeCenter_mem_drawing s)
  · exact Set.disjoint_left.mp (G.closedRhombus_disjoint_unbounded_face ht D outer houter)
      (D.openRegion_subset_closedRegion hm) ho

theorem MaskedSpineChain.exists_half_local_banks {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (hcut : cut∈G.ordinaryTrackComponents) {s b g h finish : OrientedEdge G}
    (hsb : TrackCutStep cut s b) (tail : MaskedSpineChain G cut b g) (hs : SpineSource s)
    (hext : ¬Bornology.IsBounded (G.sourceFace s).val)
    (htop : ¬∃a,PositiveCellStep finish a)
    (hfull : Relation.ReflTransGen PositiveCellStep s finish)
    (hne : edgeComponent s≠cut) (C : RhombusCell G)
    (hG : g.val=(C.a,C.b)) (hH : h.val=(C.d,C.c)) (hpos : 0<cross2 C.u C.v)
    (hAD : edgeComponent C.edgeAD=cut) :
    let p := MaskedSpineChain.cons s b g hsb tail
    ∃ loop : PlaneChain (edgeCenter s) (edgeCenter s),
      p.positive.toPlane.trace⊆loop.trace ∧
      loop.trace⊆(trackSpineTrace (edgeComponent s)∪trackSpineTrace cut)∪B.outer.val ∧
      (∀ sign : ℝ, sign=1 ∨ sign= -1 → Disjoint (p.positive.bankRegion sign) loop.trace) ∧
      p.positive.bankLabel loop (-1)=p.positive.bankLabel loop 1+1 := by
  let p := MaskedSpineChain.cons s b g hsb tail
  obtain ⟨close,hclose⟩ := B.source_prefix_closing_chain ht hcut hext C hAD
  let loop := p.positive.toPlane.append close
  have hgc : edgeComponent g=edgeComponent s := (positive_path_component p.positive.reach).symm
  have hseg : segment ℝ (edgeCenter g) C.center⊆trackSpineTrace (edgeComponent s) := by
    have hgeq : g=C.edgeAB := Subtype.ext hG
    have hheq : h=C.edgeDC := Subtype.ext hH
    have hm : C.center=stepCenter g h := by rw [hgeq,hheq,C.stepCenter_eq]
    have hmid : C.center∈segment ℝ (edgeCenter g) (edgeCenter h) := by
      rw [hm,segment_eq_image]
      refine ⟨1/2,⟨by norm_num,by norm_num⟩,?_⟩
      dsimp [stepCenter,RhombusCell.midpoint2]
      module
    have hsub := (convex_segment (𝕜 := ℝ) (edgeCenter g) (edgeCenter h)).segment_subset
      (left_mem_segment ℝ _ _) hmid
    exact fun z hz => Or.inr ⟨g,h,hgc,⟨C,hG,hH,hpos⟩,hsub hz⟩
  have hsupport : loop.trace⊆(trackSpineTrace (edgeComponent s)∪trackSpineTrace cut)∪B.outer.val := by
    rw [PlaneChain.trace_append]
    apply Set.union_subset (fun _ hz => Or.inl (Or.inl (p.positive.trace_subset_track hz)))
    intro z hz
    rcases hclose hz with (hv | hu) | (he | ho)
    · exact Or.inl (Or.inl (hseg hv))
    · exact Or.inl (Or.inr hu)
    · exact Or.inl (Or.inl (Or.inl ⟨s,rfl,Set.mem_singleton_iff.mp he⟩))
    · exact Or.inr ho
  have hdis := p.bankRegion_avoids_two_spine_loop ht hs htop hfull hne B.outer B.outer_unbounded
    loop hsupport
  have hmclose := tail.first_midpoint_not_closing ht hsb hne C hG hH hpos B.outer B.outer_unbounded close hclose
  have hmtail : stepCenter s b∉tail.positive.toPlane.trace := by
    intro hz
    have hh := (tail.positive.height_bounds hz).1
    rw [← hsb.to_positive.to_cellStep.vector_eq] at hh
    linarith [hsb.to_positive.midpoint_height_between.2]
  have hm : (1/2:ℝ) • (edgeCenter s+edgeCenter b)∉(tail.positive.toPlane.append close).trace := by
    rw [PlaneChain.trace_append]
    exact fun hz => hz.elim hmtail hmclose
  have hneMid : edgeCenter s≠edgeCenter b := by
    intro h
    have hh : edgeHeight s=edgeHeight b := by
      unfold edgeHeight
      rw [hsb.to_positive.to_cellStep.vector_eq,h]
    exact (ne_of_lt hsb.to_positive.height_lt) hh
  obtain ⟨ε,hε,hjump⟩ := PlaneChain.segment_loop_winding_jump hneMid (tail.positive.toPlane.append close) hm
  have hloop : loop=(PlaneChain.single (edgeCenter s) (edgeCenter b)).append
      (tail.positive.toPlane.append close) := rfl
  refine ⟨loop,?_,hsupport,hdis,?_⟩
  · change p.positive.toPlane.trace⊆(p.positive.toPlane.append close).trace
    rw [PlaneChain.trace_append]
    exact Set.subset_union_left
  · apply p.positive.bankLabel_difference_of_disjoint ht loop hdis Relation.ReflTransGen.refl
      (show segment ℝ (edgeCenter s) (edgeCenter b)⊆p.positive.toPlane.trace from Set.subset_union_left)
      hsb.to_positive ε hε
    intro r hr hre
    rw [hloop]
    exact (hjump r hr hre).2.2.1

end Swanepoel
