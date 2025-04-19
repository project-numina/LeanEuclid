import SystemE
import SystemE.Meta.EAuto
import Smt
import Smt.Auto

set_option maxHeartbeats 500000
#check angle_symm

set_option auto.native true

attribute [rebind Auto.Native.solverFunc] Smt.smtSolverFunc

namespace Elements.Book1

theorem proposition_1 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| :=
by
  euclid_intros
  obtain ⟨BCD, h1⟩ := circle_from_points a b (by eauto)
  obtain ⟨ACE, h2⟩ := circle_from_points b a (by eauto)
  obtain ⟨c, hc⟩ := intersection_circles BCD ACE (by
    eauto [h1, h2])
  have hBCD := point_on_circle_onlyif a b c BCD (by eauto [h1, h2, hc])
  have hACE := point_on_circle_onlyif b a c ACE (by eauto [h1, h2, hc])
  use c
  eauto [h1, h2, hc, hBCD, hACE]

-- theorem proposition_1' : ∀ (a b x : Point) (AB : Line),
--   distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) →
--   ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| ∧ (c.opposingSides x AB) :=
-- by
--   euclid_intros
--   euclid_apply circle_from_points a b as BCD
--   euclid_apply circle_from_points b a as ACE
--   euclid_apply intersection_opposite_side BCD ACE x a b AB as c
--   euclid_apply point_on_circle_onlyif a b c BCD
--   euclid_apply point_on_circle_onlyif b a c ACE
--   use c
--   euclid_finish

-- end Elements.Book1
