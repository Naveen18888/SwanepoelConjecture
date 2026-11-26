module
public import Swanepoel.TrackCutWindingCompatibilityLoop
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PlaneChain.trace_preconnected {a b : Plane} (p : PlaneChain a b) :
    IsPreconnected p.trace := by
  induction p with
  | nil a => exact isPreconnected_singleton
  | cons a b c p ih =>
    exact (convex_segment (𝕜 := ℝ) a b).isPreconnected.union'
      ⟨b,right_mem_segment ℝ a b,p.start_mem_trace⟩ ih

theorem complete_spine_height_injective {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G}
    (hs : ¬∃g,PositiveCellStep g s) (htop : ¬∃g,PositiveCellStep t g)
    (hst : Relation.ReflTransGen PositiveCellStep s t) :
    Set.InjOn (cross2 (carriedVector s)) (trackSpineTrace (edgeComponent s)) := by
  by_cases heq : s=t
  · subst t
    rw [complete_spine_trace_with_start ht hs htop hst,positiveSpineTrace_refl,union_empty]
    intro x hx y hy _
    exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
  · have htrans : Relation.TransGen PositiveCellStep s t := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hst with h | h
      · exact False.elim (heq h.symm)
      · exact h
    obtain ⟨p,hmono,hrange⟩ := positive_spine_simple_path ht htrans
    have hsMem := onSpine_center_mem_trace htrans
      (show OnSpine s t s from ⟨Relation.ReflTransGen.refl,hst⟩)
    have htrace : trackSpineTrace (edgeComponent s)=Set.range p := by
      rw [complete_spine_trace_with_start ht hs htop hst,
        union_eq_right.mpr (singleton_subset_iff.mpr hsMem),hrange]
    rw [htrace]
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ hh
    exact congrArg p (hmono.injective hh)

theorem PennyGraph.closedRhombus_disjoint_unbounded_face {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (C : RhombusCell G) (F : PlaneFace G)
    (hF : ¬Bornology.IsBounded F.val) : Disjoint C.closedRegion F.val := by
  apply Set.disjoint_left.mpr
  intro z hz hzF
  rcases C.closedRegion_subset_open_union_boundary ht hz with hO | hB
  · have heq : F.val=C.openRegion :=
      (F.property.eq_component hzF).trans ((C.isBoundedFace ht).1.eq_component hO).symm
    exact hF (heq.symm ▸ (C.isBoundedFace ht).2)
  · exact G.face_subset_complement F hzF (C.boundary_subset_drawing hB)

theorem PositiveCellStep.translated_segment_in_cell {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {e f : OrientedEdge G} (hef : PositiveCellStep e f)
    {z : Plane} (hz : z∈segment ℝ (edgeCenter e) (edgeCenter f))
    {δ : ℝ} (hδ : |δ|≤1/2) :
    ∃ C : RhombusCell G, z+δ • carriedVector e∈C.closedRegion := by
  obtain ⟨C,he,hf,_⟩ := hef
  rw [segment_eq_image] at hz
  obtain ⟨r,⟨hr0,hr1⟩,rfl⟩ := hz
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hp : (1-r) • edgeCenter e+r • edgeCenter f+δ • carriedVector e=
      C.cellPoint (1/2+δ) r := by
    simp only [edgeCenter,he,hf,carriedVector,RhombusCell.midpoint2,
      RhombusCell.cellPoint,RhombusCell.u,RhombusCell.v]
    rw [hc]
    module
  refine ⟨C,?_⟩
  rw [hp]
  have hd := abs_le.mp hδ
  exact ⟨by rw [C.coordU_cellPoint ht]; linarith,
    by rw [C.coordU_cellPoint ht]; linarith,
    by rwa [C.coordV_cellPoint ht],by rwa [C.coordV_cellPoint ht]⟩

theorem PositiveSpineChain.translated_trace_in_drawing_or_cell {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    {z : Plane} (hz : z∈p.toPlane.trace) {δ : ℝ} (hδ : |δ|≤1/2) :
    z+δ • carriedVector s∈G.drawing ∨
      ∃ C : RhombusCell G, z+δ • carriedVector s∈C.closedRegion := by
  induction p with
  | nil s =>
    rw [Set.mem_singleton_iff.mp hz]
    left
    have he : edgeCenter s+δ • carriedVector s=
        G.edgePoint s.val.1 s.val.2 (1/2+δ) := by
      simp only [edgeCenter,carriedVector,RhombusCell.midpoint2,PennyGraph.edgePoint]
      module
    rw [he]
    have hd := abs_le.mp hδ
    exact G.edgeTrace_subset_drawing _ _ s.property
      ⟨1/2+δ,⟨by linarith,by linarith⟩,rfl⟩
  | cons s e t h p ih =>
    rcases hz with hz | hz
    · exact Or.inr (h.translated_segment_in_cell ht hz hδ)
    · rw [h.to_cellStep.vector_eq]
      exact ih hz

theorem PositiveSpineChain.translated_trace_avoids_outer {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    {z : Plane} (hz : z∈p.toPlane.trace) {δ : ℝ} (hδ : |δ|≤1/2) :
    z+δ • carriedVector s∉outer.val := by
  intro hout
  rcases p.translated_trace_in_drawing_or_cell ht hz hδ with hdraw | ⟨C,hC⟩
  · exact G.face_subset_complement outer hout hdraw
  · exact Set.disjoint_left.mp (G.closedRhombus_disjoint_unbounded_face ht C outer houter) hC hout

theorem complete_spine_translated_point_not_on_spine {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G}
    (hs : ¬∃g,PositiveCellStep g s) (htop : ¬∃g,PositiveCellStep t g)
    (hst : Relation.ReflTransGen PositiveCellStep s t)
    {z : Plane} (hz : z∈trackSpineTrace (edgeComponent s)) {δ : ℝ} (hδ : δ≠0) :
    z+δ • carriedVector s∉trackSpineTrace (edgeComponent s) := by
  intro htrans
  have hheight : cross2 (carriedVector s) (z+δ • carriedVector s)=
      cross2 (carriedVector s) z := by
    rw [cross2_add_right,cross2_smul_right,cross2_self,mul_zero,add_zero]
  have heq := complete_spine_height_injective ht hs htop hst htrans hz hheight
  have hzero : δ • carriedVector s=0 := by
    have hh := add_left_cancel (show z+δ • carriedVector s=z+0 by simpa using heq)
    exact hh
  rcases smul_eq_zero.mp hzero with hh | hh
  · exact hδ hh
  · have hn := carriedVector_norm s
    rw [hh,norm_zero] at hn
    norm_num at hn

def PositiveSpineChain.bankRegion {n : ℕ} {G : PennyGraph n} {s t : OrientedEdge G}
    (p : PositiveSpineChain G s t) (sign : ℝ) : Set Plane :=
  {z | ∃ x∈p.toPlane.trace, ∃ δ∈Ioc (0 : ℝ) (1/2), z=x+(sign*δ) • carriedVector s}

theorem PositiveSpineChain.bankRegion_preconnected {n : ℕ} {G : PennyGraph n}
    {s t : OrientedEdge G} (p : PositiveSpineChain G s t) (sign : ℝ) :
    IsPreconnected (p.bankRegion sign) := by
  have hprod := p.toPlane.trace_preconnected.prod (isPreconnected_Ioc (a := (0:ℝ)) (b := 1/2))
  have himg := hprod.image
    (fun q : Plane×ℝ => q.1+(sign*q.2) • carriedVector s)
    (continuous_fst.add ((continuous_const.mul continuous_snd).smul continuous_const)).continuousOn
  convert himg using 1
  ext z
  constructor
  · rintro ⟨x,hx,δ,hδ,rfl⟩
    exact ⟨(x,δ),⟨hx,hδ⟩,rfl⟩
  · rintro ⟨⟨x,δ⟩,⟨hx,hδ⟩,rfl⟩
    exact ⟨x,hx,δ,hδ,rfl⟩

theorem PositiveSpineChain.bankRegion_avoids_loop {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : ¬∃g,PositiveCellStep g s) (htop : ¬∃g,PositiveCellStep t g)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (loop : PlaneChain (edgeCenter s) (edgeCenter s))
    (hloop : loop.trace⊆trackSpineTrace (edgeComponent s)∪outer.val)
    (sign : ℝ) (hsign : sign=1 ∨ sign= -1) : Disjoint (p.bankRegion sign) loop.trace := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,δ,hδ,rfl⟩ hz
  have hxS := p.trace_subset_track hx
  have hn : sign*δ≠0 := by rcases hsign with rfl | rfl <;> nlinarith [hδ.1]
  have hb : |sign*δ|≤1/2 := by
    rcases hsign with rfl | rfl <;> simp only [one_mul,neg_mul,abs_neg,abs_of_pos hδ.1] <;> exact hδ.2
  rcases hloop hz with hspine | hout
  · exact complete_spine_translated_point_not_on_spine ht hs htop p.reach hxS hn hspine
  · exact p.translated_trace_avoids_outer ht outer houter hx hb hout

end Swanepoel
