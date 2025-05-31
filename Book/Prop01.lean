import SystemE
import Smt.Real


-- set_option trace.smt true

namespace Elements.Book1

-- self reference test
-- theorem womp : ∀ (A B C D : Point), (A = B) → ∠ A:B:C = ∠ C:D:A := by
--   euclid_intros
--   euclid_apply womp
--   euclid_finish


theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
  euclid_intros
  obtain ⟨BCD, h1⟩ := circle_from_points a b (by esmt (timeout := 100))
  obtain ⟨ACE, h2⟩ := circle_from_points b a (by esmt)
  -- euclid_apply proposition_1
  obtain ⟨c, hc⟩ := intersection_circles BCD ACE (by esmt)
  have hBCD := point_on_circle_onlyif a b c BCD (by esmt)
  have hACE := point_on_circle_onlyif b a c ACE (by esmt [h1, h2, hc])
  use c
  esmt [h1, h2, hc, hBCD, hACE]


theorem proposition_1' : ∀ (a b x : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
by
  euclid_intros
  euclid_apply circle_from_points a b as BCD
  euclid_apply circle_from_points b a as ACE
  euclid_apply intersection_opposite_side BCD ACE x a b AB as c
  euclid_apply point_on_circle_onlyif a b c BCD
  euclid_apply point_on_circle_onlyif b a c ACE
  use c
  euclid_finish


end Elements.Book1
