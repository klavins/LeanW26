
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Introduction.lean'>Code</a> for this chapter</span>


# Foundations in Lean
by Eric Klavins

The notes presented here were initially developed for a special topics graudate course on Lean I taught in the Winter of 2025. The course was taken mainly by Electrical and Computer Engineers with standard programming experience, some engineering mathematics background, and a variety of different application areas in mind. The main reading for the course included all the standard Lean references and books. These notes are merely a supplement for those excellent resources.

That said, I hope the material presented here presents a unique and useful perspective that arose over several decades of my periodically checking in on proof assistants, becoming enamored for a while, and then moving on to other projects. For me, the alure of theorem provers is the possibility of once and for all connecting the foundations of mathematics (Type Theory in the case of Lean) with the work of practicing mathematicians and engineers. Thus, my presentation focuses on foundations, whereas other resources may focus more on the use of Lean for particular applications.

Every new generation of proof assistant gets a bit closer to realizing the goal of making all of mathematics easily formalized. Of all of the tools available, from Agda to Rocq, none has captured my attention like Lean 4 has. I think it is the combination of tooling in VS Code, the self-boostrapping nature of Lean 4 being written in Lean 4, the simultaneous blossoming of machine learning, and the inspiring community of researchers exploring how to use Lean 4. These taken together seem to be giving Lean considerable momentum.

My hope is that these notes are useful for students wishing to understand the type theoretic foundations of Lean and similar tools. I think such an understanding is useful for a variety of reasons. First, I think learning a computer programming language is aided by an understanding of how the language is executed or intepreted. For a language like C, it is hard to imagine becoming a true expert without understanding assembly language, stacks, memory allocation, and compilation. Just using a C debugger like `gdb` requires a fair amount of knowledge about the underlying model of computation. For Lean, the model is the lambda calculus, type checking, and type inference. When Lean doesn't work, students can spend hours trying various incantations to make it do what they want. With some understanding of the underlying model of computation, getting unstuck becomes easier. Second, there is no reason to think that the development of proof checkers is somehow complete with Lean as the final solution to the problems that have plagued such tools for decades. Understanding how Lean works will hopefully inspire someone (perhaps even me) to write their own proof checker someday, using Lean and its foundations as a reference architecture.

Finally, the study of the foundations of mathematics is incredibly rich and interesting in its own right, like topology or number theory. I encourage the interested student to dig deeply into this material and then read the primary literature on Type Theory, to gain at least an appreciation if not a mastery of the wonders that underpin how Lean and its cohort of proof checkers work.

## Acknowledgements

I would like to acknowledge the students who took my special topics course offered the Winter of 2025 at the University of Washington. We all learned Lean together. At first, I was a few weeks ahead, and by the end of the course I was a few weeks behind. Much of the material here was developed in response to their questions and ideas.



<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
