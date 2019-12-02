progs: CreateSemCatalogue CreateSynCatalogue Effect MrE Reg Test Tim Tom

CreateSemCatalogue: Alphabet.hs Catalogue.hs Comparison.hs Context.hs \
CreateSemCatalogue.hs Expression.hs Function.hs Fuse.hs Generator.hs \
Info.hs List.hs OK.hs PreOrderTrees.hs Pressing.hs Queue.hs \
Shrinking.hs StarPromotion.hs OneLetterFactorization.hs
	ghc -O CreateSemCatalogue

CreateSynCatalogue: Alphabet.hs Comparison.hs Context.hs CreateSynCatalogue.hs \
Derivative.hs Expression.hs Function.hs Fuse.hs Generator.hs Info.hs List.hs \
OK.hs PreOrderTrees.hs Pressing.hs Queue.hs Shrinking.hs \
StarPromotion.hs SyntaxCatalogue.hs OneLetterFactorization.hs
	ghc -O CreateSynCatalogue

Effect: Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Effect.hs \
Expression.hs Function.hs Fuse.hs Generator.hs GruberP.hs Info.hs \
List.hs OK.hs Parser.hs PreOrderTrees.hs Pressing.hs Queue.hs \
Shrinking.hs StarPromotion.hs Stellation.hs Parameters.hs OneLetterFactorization.hs \
SyntaxCatalogue.hs semcatalogue syncatalogue populations
	ghc -O Effect
ifndef OS
	chmod +x allEffect
endif

effects: Effect allEffect populations
ifndef OS
	if test -d "effects" ; then rm effects/* ; else mkdir effects ; fi
	./allEffect
	touch effects
else
	allEffect.cmd
endif

MrE: Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Expression.hs \
Function.hs Fuse.hs Generator.hs GruberP.hs Info.hs List.hs MrE.hs \
OK.hs Parser.hs PreOrderTrees.hs Pressing.hs Queue.hs \
Shrinking.hs StarPromotion.hs Stellation.hs Parameters.hs OneLetterFactorization.hs \
SyntaxCatalogue.hs semcatalogue syncatalogue
	ghc -O MrE

laboratory: Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs \
Expression.hs Function.hs Fuse.hs Generator.hs Info.hs Laboratory.hs List.hs \
Metrics.hs OK.hs PreOrderTrees.hs Pressing.hs Properties.hs Queue.hs \
Shrinking.hs StarPromotion.hs Stellation.hs OneLetterFactorization.hs \
SyntaxCatalogue.hs semcatalogue syncatalogue
	ghc -O Laboratory.hs
ifndef OS
	touch laboratory
	chmod +x laboratory
endif

populations: Reg allReg
ifndef OS
	if test -d "populations" ; then rm populations/* ; else mkdir populations ; fi
	./allReg
	touch populations
else
	allReg.cmd
endif

Reg: BigNum.hs RegexpCount.hs Reg.hs
	ghc -O Reg
ifndef OS
	chmod +x allReg
endif

semcatalogue: CreateSemCatalogue
ifndef OS
	if test -d "semcatalogue" ; then rm semcatalogue/* ; else mkdir semcatalogue ; fi
	./CreateSemCatalogue
	touch semcatalogue
else
	semcatalogue.cmd
endif

syncatalogue: CreateSynCatalogue
ifndef OS
	if test -d "syncatalogue" ; then rm syncatalogue/* ; else mkdir syncatalogue ; fi
	./CreateSynCatalogue
	touch syncatalogue
else
	syncatalogue.cmd
endif

Tim: Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Expression.hs \
Function.hs Fuse.hs Generator.hs Info.hs List.hs OK.hs PreOrderTrees.hs \
Pressing.hs Queue.hs Shrinking.hs StarPromotion.hs \
SyntaxCatalogue.hs Tim.hs TopShrink.hs Parameters.hs OneLetterFactorization.hs \
semcatalogue syncatalogue
	ghc -O Tim

Tom: Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Expression.hs \
Function.hs Fuse.hs Generator.hs Info.hs List.hs OK.hs PreOrderTrees.hs \
Pressing.hs Queue.hs Shrinking.hs StarPromotion.hs \
SyntaxCatalogue.hs Tom.hs TopShrink.hs Parameters.hs OneLetterFactorization.hs \
semcatalogue syncatalogue
	ghc -O Tom

runTimes.pdf: runTimes.tex runTimesTables.tex
	pdflatex runTimes.tex

runTimesTables.tex: runTimes MrE populations
	./runTimes > runTimesTables.tex

sizeRatios.pdf: sizeRatios.tex sizeRatiosTables.tex
	pdflatex sizeRatios.tex

sizeRatiosTables.tex: sizeRatios MrE populations
	./sizeRatios > sizeRatiosTables.tex

Test: List.hs Expression.hs Info.hs Catalogue.hs Context.hs Comparison.hs Fuse.hs \
Parameters.hs Pressing.hs Stellation.hs StarPromotion.hs SyntaxCatalogue.hs Test.hs
	ghc -O Test.hs
