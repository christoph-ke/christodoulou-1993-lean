module

public import ChristodoulouBV.Existence.Lemma62CounterexamplesL1
public import ChristodoulouBV.Existence.Lemma62CounterexamplesLSC

/-!
# Two counterexamples to the printed Lemma 6.2 (Christodoulou 1993, p. 1189)

* `lemma6_2_L1_conclusion_false`: every premise holds but the section
  functional has infinite integral.
* `lemma6_2_lsc_step_false`: every premise holds but lower semicontinuity
  fails at a nonexceptional accumulation point of exceptional sections.

Both statements use exactly the premises of `lemma6_2_lintegral`, bundled
in `Lemma62Hypotheses`, and its pointwise primitive and interval carriers.
The second example has a measurable functional; it refutes the printed
lower-semicontinuity step without asserting failure of measurability.
-/

public section
