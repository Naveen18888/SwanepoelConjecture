module
public import Swanepoel.ContactFaces
public import Swanepoel.EulerLeaf
public import Mathlib.Analysis.Normed.Module.Connected
@[expose] public section

noncomputable section
namespace Swanepoel
open Set Metric
attribute [local instance] Classical.propDecidable

theorem punctured_plane_ball_preconnected (p : Plane) (r : ℝ) :
    IsPreconnected (Metric.ball p r \ {p}) := by
  have hsp := isPreconnected_sphere
    (Module.one_lt_rank_of_one_lt_finrank (by norm_num [Plane])) (0 : Plane) 1
  have hprod := hsp.prod (isPreconnected_Ioo (a := (0 : ℝ)) (b := r))
  have himage := hprod.image (fun x : Plane × ℝ => p+x.2 • x.1)
    (continuous_const.add (continuous_snd.smul continuous_fst)).continuousOn
  have heq : (fun x : Plane × ℝ => p+x.2 • x.1) ''
      (Metric.sphere (0 : Plane) 1 ×ˢ Ioo (0 : ℝ) r) = Metric.ball p r \ {p} := by
    ext z
    constructor
    · rintro ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
      have hun : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
      have hdist : dist (p+t • u) p = t := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hun,
          Real.norm_eq_abs, abs_of_pos ht.1, mul_one]
      refine ⟨?_, ?_⟩
      · change dist (p+t • u) p < r
        rw [hdist]
        exact ht.2
      · intro he
        have heq : p+t • u=p := Set.mem_singleton_iff.mp he
        rw [heq,dist_self] at hdist
        linarith [ht.1]
    · rintro ⟨hz,hne⟩
      have hz' : z ≠ p := by simpa only [Set.mem_singleton_iff] using hne
      have hd : 0 < ‖z-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz')
      let u := ‖z-p‖⁻¹ • (z-p)
      have hun : ‖u‖ = 1 := by
        simp [u, norm_smul, hd.ne']
      refine ⟨(u,‖z-p‖),⟨?_,hd,?_⟩,?_⟩
      · simpa only [Metric.mem_sphere, dist_zero_right] using hun
      · simpa only [Metric.mem_ball, dist_eq_norm] using hz
      · dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
        abel
  rwa [heq] at himage

private theorem component_closure_in_ambient (U : Set Plane) {p z : Plane}
    (hp : p ∈ U) (hz : z ∈ closure (connectedComponentIn U p)) (hzU : z ∈ U) :
    z ∈ connectedComponentIn U p := by
  rw [connectedComponentIn_eq_image hp] at hz ⊢
  have hc := (Topology.IsInducing.subtypeVal (t := U)).closure_eq_preimage_closure_image
    (connectedComponent (⟨p,hp⟩ : U))
  have hz' : (⟨z,hzU⟩ : U) ∈ closure (connectedComponent (⟨p,hp⟩ : U)) := by
    rw [hc]
    exact hz
  exact ⟨⟨z,hzU⟩, isClosed_connectedComponent.closure_subset hz', rfl⟩

theorem PennyGraph.IsSubFace.frontier_subset_subdrawing {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F) :
    frontier F ⊆ G.subdrawing S := by
  intro z hz
  rw [frontier, hf.isOpen.interior_eq] at hz
  by_contra hzd
  obtain ⟨x,hx,hF⟩ := hf
  have hcl : z ∈ closure (connectedComponentIn (G.subdrawing S)ᶜ x) := by
    rw [← hF]
    exact hz.1
  exact hz.2 (hF ▸ component_closure_in_ambient _ hx hcl hzd)

theorem linear_no_open_max (l : Plane →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    {U : Set Plane} (hU : IsOpen U) {x : Plane} (hx : x ∈ U)
    (hmax : ∀ y ∈ U, l y ≤ l x) : False := by
  have hex : ∃ u, l u ≠ 0 := by
    by_contra hn
    apply hl
    apply LinearMap.ext
    intro u
    by_contra hu
    exact hn ⟨u,hu⟩
  obtain ⟨u,hu⟩ := hex
  let w := (l u)⁻¹ • u
  have hw : l w = 1 := by simp [w, hu]
  have hcont : Continuous (fun t : ℝ => x+t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen ((fun t : ℝ => x+t • w) ⁻¹' U) := hU.preimage hcont
  have hzero : (0 : ℝ) ∈ ((fun t : ℝ => x+t • w) ⁻¹' U) := by simpa using hx
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have hmem : r/2 ∈ Metric.ball (0 : ℝ) r := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0<r/2)]
    linarith
  have h := hmax (x+(r/2) • w) (hball hmem)
  rw [map_add,map_smul,hw,smul_eq_mul,mul_one] at h
  linarith

theorem PennyGraph.IsSubFace.no_max_at_isolated_vertex {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F)
    (l : Plane →ₗ[ℝ] ℝ) (hl : l ≠ 0) (v : Fin n)
    (hv : ∀ e ∈ S, e.val.1 ≠ v ∧ e.val.2 ≠ v)
    (hcl : G.point v ∈ closure F)
    (hmax : ∀ z ∈ closure F, l z ≤ l (G.point v)) : False := by
  obtain ⟨r,hr,_,hfree⟩ := G.isolated_vertex_free_ball S v hv
  have hB : Metric.ball (G.point v) r \ {G.point v} ⊆ (G.subdrawing S)ᶜ := by
    intro z hz hzd
    exact hz.2 (hfree z hz.1 hzd)
  have hvnot : G.point v ∉ F := by
    obtain ⟨x,hx,hF⟩ := hf
    rw [hF]
    intro h
    exact connectedComponentIn_subset _ _ h (Or.inl ⟨v,rfl⟩)
  obtain ⟨y,hyBall,hyF⟩ := mem_closure_iff.mp hcl (Metric.ball (G.point v) r)
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hyB : y ∈ Metric.ball (G.point v) r \ {G.point v} := by
    refine ⟨hyBall,?_⟩
    intro heq
    exact hvnot ((Set.mem_singleton_iff.mp heq) ▸ hyF)
  have hBF : Metric.ball (G.point v) r \ {G.point v} ⊆ F := by
    have h := (punctured_plane_ball_preconnected (G.point v) r).subset_connectedComponentIn hyB hB
    rwa [← hf.eq_component hyF] at h
  apply linear_no_open_max l hl Metric.isOpen_ball (Metric.mem_ball_self hr)
  intro z hz
  by_cases heq : z = G.point v
  · rw [heq]
  · exact hmax z (subset_closure (hBF ⟨hz,heq⟩))

theorem PennyGraph.IsSubFace.linear_support {n : ℕ} {G : PennyGraph n}
    {S : Finset (ContactEdge G)} {F : Set Plane} (hf : G.IsSubFace S F)
    (hb : Bornology.IsBounded F) (l : Plane →ₗ[ℝ] ℝ) (hl : l ≠ 0) (M : ℝ)
    (hends : ∀ e ∈ S, l (G.point e.val.1) ≤ M ∧ l (G.point e.val.2) ≤ M) :
    ∀ z ∈ F, l z ≤ M := by
  obtain ⟨x,hx,hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    hf.nonempty.closure l.continuous_of_finiteDimensional.continuousOn
  suffices hxM : l x ≤ M from fun z hz => (hmax (subset_closure hz)).trans hxM
  by_contra hbad
  have hMx : M < l x := lt_of_not_ge hbad
  have hxnotF : x ∉ F := by
    intro hxF
    exact linear_no_open_max l hl hf.isOpen hxF
      (fun y hy => hmax (subset_closure hy))
  have hxdraw := hf.frontier_subset_subdrawing
    (show x ∈ frontier F by rw [frontier,hf.isOpen.interior_eq]; exact ⟨hx,hxnotF⟩)
  have hxnoedge : ∀ e ∈ S, x ∉ G.edgeTrace e.val.1 e.val.2 := by
    intro e he hxedge
    obtain ⟨t,⟨ht0,ht1⟩,hpoint⟩ := hxedge
    have hlin : l x = (1-t)*l (G.point e.val.1)+t*l (G.point e.val.2) := by
      rw [← hpoint]
      simp only [PennyGraph.edgePoint,map_add,map_smul,smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hends e he).1 (sub_nonneg.mpr ht1)
    have h2 := mul_le_mul_of_nonneg_left (hends e he).2 ht0
    nlinarith
  rcases hxdraw with ⟨v,hv⟩ | he
  · subst x
    apply hf.no_max_at_isolated_vertex l hl v ?_ hx
      (fun z hz => hmax hz)
    intro e he
    constructor
    · intro hev
      apply hxnoedge e he
      exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint,hev]⟩
    · intro hev
      apply hxnoedge e he
      exact ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint,hev]⟩
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp he
    obtain ⟨heS,he⟩ := Set.mem_iUnion.mp he
    exact hxnoedge e heS he

end Swanepoel
