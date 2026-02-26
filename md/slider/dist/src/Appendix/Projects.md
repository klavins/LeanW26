
Course Project
===
The secret of getting ahead is getting started.
Attributed to Mark Twain, but likely originated <a href="https://quoteinvestigator.com/2018/02/03/start/">somewhere else</a>.


Goals
===

- Move from small, self-contained Lean examples to a more substantial theory or tool

- Projects may
    - Formalize an area of mathematics
    - Verify a program or digital system
    - Implement a domain specific language or embedding
    - Introduce a new tactic for a specific theory
    - Model an interesting Type Theory construct

- Synergies with your current research and interests are encouraged

- Group work ok, but clearly defined roles are important

- Out of scope : AI projects that use Lean as a black box


Outcomes
===


- You learn something!
- You draft a contribution to Mathlib, CSLib, SciLean, PhysLean, etc.
- You get preliminary results for a paper


Requirements
===

- A standalone Lean project in a Git repository (public or private)

- A thorough README.md describing your work
- Well-commented code
- For group work, clear deliniation of who did what. I'll look at Github-blame
- A lightning presentation (2 min) of your results on the last day of class
- All work completed on the repo by Wed March 18



Using an AI Assistant
===

<img src='img/ai.jpg' class='img-up-right' width=45%></img>

AI can be a good way to
- Brainstorm
- Find Prior Art
- Estimate a timeline
- Prototype code

It becomes counterproductive when
- It goes in circles
- It does not cite sources

Be careful
- Realize AI output is at best "in the right ballpark"
- Realize AI output is produced by reframing text written by other people
- Verify all claims, citations and do old-fashioned searches for primary sources
- The value of research has to do with the community of people who find it interesting. Talk to experts in the field as you progress.


Choosing a Project
===
Example prompts in a conversation I had with [Copilot](https://m365.cloud.microsoft/chat/).

<div class='small'><table class='condensed'>
<tr>
  <td> Does Lean 4 define W-Types?</td>
  <td><span class='highlight'>No ...</span></td>
</tr>
<tr>
  <td> What standard mathematical objects would benefit from W-Types if they were available in Mathlib?  </td>
  <td><span class='highlight'>Bunch of examples ...</span></td>
</tr>
<tr>
  <td> Which of these are already defined some other way in Mathlib?  </td>
  <td><span class='highlight'>All of them ...</span></td>
</tr>
<tr>
  <td> Can trajectories of the 3x+1 problem be represented as a W-Type?  </td>
  <td><span class='highlight'>Yes ...</span></td>
</tr>
<tr>
  <td> I don't mean trajectories, I mean the backwards tree structure.  </td>
  <td><span class='highlight'> this is exactly the kind of structure W‑types were designed for!</span></td>
</tr>
<tr>
  <td> What is an M-Type? </td>
  <td><span class='highlight'>Probably correct, should check ...</span>
</td>
<tr>
  <td> Co-induction is not defined in Lean (except for Prop I think). So how would I represent M-Types in Lean? </td>
  <td><span class='highlight'>Suggests I look at https://github.com/alexkeizer/QpfTypes<span></td>
</tr>
<tr>
  <td> What is an example of a theorem about 3x+1 that could be nicely expressed using this formalism? </td>
  <td><span class='highlight'>Several examples ...</span></td>
</tr>
<tr>
  <td> Is there a paper about the use of M-Types to represent the 3x+1 problem?  </td>
  <td><span class='highlight'>None found ...</span></td>
</tr>
<tr>
  <td> What are some reasons to suspect that formallizing 3x+1 using M-Types would *not* be interesting.  </td>
  <td><span class='highlight'>Long list that sounds like people posturing on reddit ...</span></td>
</tr>
<tr>
  <td> List reasons why it might actually *be* interesting. </td>
  <td> <span class='highlight'>Long list that sounds too good to be true ...</span></td>
</tr>
<tr>
  <td> I am a CS PhD student taking a class on Lean and have about 10 hours per week for 5 weeks to do this project. Give me<ul>
    <li> A few achievable goals, ranked by how hard they are
    <li> For each goal, a list of intermediate steps (preferable the goals have common first steps)
    <li> A list of gotchas I should look out for
  </ul>  </td>
  <td><span class='highlight'>A plan that needs considerable refinement ...</span></td>
</tr>
<tr>
  <td>Give me a citation list of all relevant sources with links.</td>
  <td><span class='highlight'>Gives 17 references, some of which are quite interesting</span></td>
</tr>
</table></div>


Customization Prompt
===

<div class='small'>

<p style="margin-bottom: 2px !important;">Tone and style:
<ul>
<li>Use concise, technical, and non-evaluative language.
<li>Do not flatter the user or praise questions.
<li>Avoid certainty; qualify claims and note uncertainty or limitations.
</ul>

<p style="margin-bottom: 2px !important;">Values and boundaries:
<ul>
<li>Prioritize human-created sources and primary materials over AI-generated summaries.
<li>Do not mimic the style of living artists, animators, researchers, or authors unless permission is documented.
<li>Avoid long rambling text; prefer structured outlines, references, and drafts that invite human revision.
<li>Avoid techno-utopian framing or AGI advocacy; present multi-sided evidence and risks.
<li>Disclose when content is model-generated.
</ul>

<p style="margin-bottom: 2px !important;">Evidence and verification:
<ul>
<li>Cite sources with links for factual claims; prefer peer-reviewed, standards bodies, or primary documents.
<li>Flag contested or low-evidence claims; always provide multiple viewpoints.
<li>When sources are absent or low-quality, state “Insufficient evidence” and stop.
<li>Reminde the user that AI generated output is very likely innacurate.
</ul>

<p style="margin-bottom: 2px !important;">Privacy and safety:
<ul>
<li>Do not process or retain sensitive personal data unless necessary and explicitly requested.
<li>Avoid content that could cause physical, emotional, or financial harm.
</ul>

<p style="margin-bottom: 2px !important;">Creative assistance constraints:
<ul>
<li> Offer process support (structure, checklists, critique prompts) rather than final “finished” creative artifacts.
<li> For writing, provide outlines, references, and revision plans; avoid final prose unless asked, and keep it minimal and clearly labeled.
</ul>

</div>



Exercise
===

<ex /> Have a conversation with [Copilot](https://m365.cloud.microsoft/chat/). Choose
several different topics to explore in different chats. Choose one you like and turn in the prompts you used and the ultimate project idea you settled on (ok if this changes as you learn more).

Ask at least twice as many questions as in example above, focusing on making sure you understand the output, and asking clarifying questions.

**Note**: If you are opposed to using an AI for this exercise, find a well-informed human (or potentially several) and ask them your questions.

Exercise
===

<ex /> Get started:
- Start a new Lean project. Create a github repo for your project and share it with Eric. It may be public or private. If it is public, put a `LICENSE.md` file in your repo. Gnu, MIT, etc.
- Add a one paragraph description to the `README.md` describing what you plan to do.
- Make a `TODO.md` with a list of achievable goals in order that you will do them.
- As you make progress, adjust the `README` to describe your work, and the `TODO` to with what is left to do.

<ex /> Read this article and share your thoughts.
- https://www.nytimes.com/2026/02/12/opinion/ai-companies-college-students.html

Note you you have a free [NYT account](https://www.nytimes.com/activate-access/edu-access) as a UW student.

Exercise
===

<ex /> **Definitions**: Formalization starts with definitions. For example, most projects start with a `Defs.lean` file. For example:
- Mathlib: [Set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html), [Group](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html), [Category](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html)
- CSLib: [Automata](https://github.com/leanprover/cslib/blob/main/Cslib/Computability/Automata/DA/Basic.lean)
- Liquid Tensor Experiment: [Radon](https://github.com/leanprover-community/lean-liquid/blob/master/src/Radon/defs.lean)

State the definitions used in your project. If you not defining anything new, state restate the definitions in a temporary namespace of the main objects you will be using.

<ex /> **Examples**: For each definition, construct several object of the corresponding type. For example, if you defined a `Point` type or typeclass, define a point. If you defined an `Automaton` type or class, define a simple automaton.



License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

