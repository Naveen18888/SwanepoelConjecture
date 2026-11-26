module
public import Swanepoel.TrackCutWindingJumpActual
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PositiveCellStep.winding_probe_neighbourhood {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {a b : OrientedEdge G} (hab : PositiveCellStep a b) :
    ∃ C : RhombusCell G, a.val=(C.a,C.b) ∧ b.val=(C.d,C.c) ∧
      ∃ δ : ℝ, 0<δ ∧ ∀ r : ℝ, |r|<δ →
        windingNormalProbe (edgeCenter a) (edgeCenter b) r∈C.openRegion := by
  obtain ⟨C,he,hf,_⟩ := hab
  have heq : a=C.edgeAB := Subtype.ext he
  have hfq : b=C.edgeDC := Subtype.ext hf
  have hmid : windingNormalProbe (edgeCenter a) (edgeCenter b) 0=C.center := by
    have hstep : stepCenter a b=C.center := by rw [heq,hfq,C.stepCenter_eq]
    simpa only [windingNormalProbe,zero_smul,add_zero,stepCenter,RhombusCell.midpoint2] using hstep
  have hU : IsOpen {r : ℝ | windingNormalProbe (edgeCenter a) (edgeCenter b) r∈C.openRegion} :=
    C.isOpen_openRegion.preimage (continuous_windingNormalProbe _ _)
  have h0 : (0 : ℝ)∈{r : ℝ | windingNormalProbe (edgeCenter a) (edgeCenter b) r∈C.openRegion} := by
    change windingNormalProbe (edgeCenter a) (edgeCenter b) 0∈C.openRegion
    rw [hmid,← C.cellPoint_half_eq_center]
    exact C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  exact ⟨C,he,hf,δ,hδ,fun r hr => hball (by simpa [Metric.mem_ball,Real.dist_eq] using hr)⟩

theorem PennyGraph.ordinary_spine_winding_jump {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {s t a b : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g)
    (hsa : Relation.ReflTransGen PositiveCellStep s a) (hab : PositiveCellStep a b)
    (hbt : Relation.ReflTransGen PositiveCellStep b t)
    (hord : edgeComponent s∈G.ordinaryTrackComponents) :
    ∃ C : RhombusCell G, a.val=(C.a,C.b) ∧ b.val=(C.d,C.c) ∧
      ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
        ∃ p : PlaneChain (edgeCenter a) (edgeCenter a),
          p.trace⊆trackSpineTrace (edgeComponent s)∪outer.val ∧
          (∀ F∈G.defectPlaneFaces ht, Disjoint F.val p.trace ∧
            ∀ z∈F.val, p.windingIndex z=G.faceWindingLabel p F) ∧
          ∃ ε : ℝ, 0<ε ∧ ∀ r : ℝ, 0<r → r<ε →
            windingNormalProbe (edgeCenter a) (edgeCenter b) r∈C.openRegion ∧
            windingNormalProbe (edgeCenter a) (edgeCenter b) (-r)∈C.openRegion ∧
            windingNormalProbe (edgeCenter a) (edgeCenter b) r∉p.trace ∧
            windingNormalProbe (edgeCenter a) (edgeCenter b) (-r)∉p.trace ∧
            p.windingIndex (windingNormalProbe (edgeCenter a) (edgeCenter b) (-r))=
              p.windingIndex (windingNormalProbe (edgeCenter a) (edgeCenter b) r)+1 ∧
            p.windingIndex (windingNormalProbe (edgeCenter a) (edgeCenter b) r)%2≠
              p.windingIndex (windingNormalProbe (edgeCenter a) (edgeCenter b) (-r))%2 := by
  obtain ⟨outer,houter,rest,hm,htrace⟩ := G.ordinary_spine_segment_loop ht hs htop hsa hab hbt hord
  have hne : edgeCenter a≠edgeCenter b := by
    intro heq
    have hh : edgeHeight a=edgeHeight b := by
      unfold edgeHeight
      rw [hab.to_cellStep.vector_eq,heq]
    exact (ne_of_lt hab.height_lt) hh
  have hm' : (1/2 : ℝ) • (edgeCenter a+edgeCenter b)∉rest.trace := hm
  obtain ⟨ε,hε,hjump⟩ := PlaneChain.segment_loop_winding_jump hne rest hm'
  obtain ⟨C,he,hf,δ,hδ,hcell⟩ := hab.winding_probe_neighbourhood ht
  let p := (PlaneChain.single (edgeCenter a) (edgeCenter b)).append rest
  refine ⟨C,he,hf,outer,houter,p,htrace,?_,min ε δ,lt_min hε hδ,?_⟩
  · intro F hF
    have hne : F≠outer := by
      intro heq
      exact houter (heq ▸ G.defectPlaneFace_isBounded ht hF)
    have hd : Disjoint F.val p.trace :=
      ((G.defectFace_disjoint_trackSpine ht F hF (edgeComponent s)).union_right
        (G.faces_disjoint_of_ne F outer hne)).mono_right htrace
    refine ⟨hd,?_⟩
    intro z hz
    have hpre : IsPreconnected F.val := by
      obtain ⟨x,hx,hcomp⟩ := F.property
      rw [hcomp]
      exact isPreconnected_connectedComponentIn
    exact p.windingIndex_constant hpre hd hz F.property.nonempty.choose_spec
  · intro r hr hrmin
    have hrε := hrmin.trans_le (min_le_left ε δ)
    have hrδ := hrmin.trans_le (min_le_right ε δ)
    have hj := hjump r hr hrε
    exact ⟨hcell r (by simpa only [abs_of_pos hr] using hrδ),
      hcell (-r) (by simpa only [abs_neg,abs_of_pos hr] using hrδ),
      hj.1,hj.2.1,hj.2.2.1,hj.2.2.2⟩

end Swanepoel
