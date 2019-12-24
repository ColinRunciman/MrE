ifndef OS
semCreate=CreateSemCatalogue
synCreate=CreateSynCatalogue
mrE=MrE
effect=Effect
reg=Reg
test=Test
tim=Tim
minratios=MinRatios
timscript=allTimes
effscript=allEffect
runtimes=RunTimes
effdata=EffectData
else
semCreate=CreateSemCatalogue.exe
synCreate=CreateSynCatalogue.exe
mrE=MrE.exe
effect=Effect.exe
reg=Reg.exe
test=Test.exe
tim=Tim.exe
minratios=MinRatios.exe
timscript=allTimes.cmd
effscript=allEffects.cmd
runtimes=RunTimes.exe
effdata=EffectData.exe
endif

progs: $(semCreate) $(synCreate) $(effect) $(mrE) $(reg) $(test) $(tim) $(minratios)

$(semCreate): Alphabet.hs Catalogue.hs Comparison.hs Context.hs \
CreateSemCatalogue.hs Expression.hs Function.hs Fuse.hs Generator.hs \
Info.hs List.hs OK.hs PreOrderTrees.hs Pressing.hs Queue.hs \
StarPromotion.hs OneLetterFactorization.hs Stellation.hs
	ghc -O CreateSemCatalogue

$(synCreate): Alphabet.hs Comparison.hs Context.hs CreateSynCatalogue.hs \
Derivative.hs Expression.hs Function.hs Fuse.hs Generator.hs Info.hs List.hs \
OK.hs PreOrderTrees.hs Pressing.hs Queue.hs \
StarPromotion.hs SyntaxCatalogue.hs OneLetterFactorization.hs Stellation.hs
	ghc -O CreateSynCatalogue

$(effect): Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Effect.hs \
Expression.hs Function.hs Fuse.hs Generator.hs GruberP.hs Info.hs \
List.hs OK.hs Parser.hs PreOrderTrees.hs Pressing.hs Queue.hs \
StarPromotion.hs Stellation.hs Parameters.hs OneLetterFactorization.hs \
SyntaxCatalogue.hs semproxy.txt synproxy.txt popproxy.txt
	ghc -O Effect
ifndef OS
	chmod +x allEffect
endif

effproxy.txt: $(effect) $(effscript) popproxy.txt
ifndef OS
	./allEffect
else
	allEffects.cmd
endif
	echo effects > effproxy.txt

timproxy.txt : $(tim) $(mre) $(timscript)
ifndef OS
	./allTimes
else
	allTimes.cmd
endif
	echo times > timproxy.txt

$(mrE): Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Expression.hs \
Function.hs Fuse.hs Generator.hs GruberP.hs Info.hs List.hs MrE.hs \
OK.hs Parser.hs PreOrderTrees.hs Pressing.hs Queue.hs \
StarPromotion.hs Stellation.hs Parameters.hs OneLetterFactorization.hs \
SyntaxCatalogue.hs semproxy.txt synproxy.txt popproxy.txt
	ghc -O MrE

ifndef OS
popproxy.txt: $(reg) allReg
	./allReg
else
popproxy.txt: $(reg) allReg.cmd
	allReg.cmd
endif
	echo population > popproxy.txt

$(reg): BigNum.hs RegexpCount.hs Reg.hs
	ghc -O Reg
ifndef OS
	chmod +x allReg
endif

semproxy.txt: $(semCreate) synproxy.txt
ifndef OS
	if test -d "semcatalogue" ; then rm semcatalogue/* ; else mkdir semcatalogue ; fi
	./CreateSemCatalogue
else
	semcatalogue.cmd
endif
	echo semcat > semproxy.txt

synproxy.txt: $(synCreate)
ifndef OS
	if test -d "syncatalogue" ; then rm syncatalogue/* ; else mkdir syncatalogue ; fi
	./CreateSynCatalogue
else
	syncatalogue.cmd
endif
	echo syncat > synproxy.txt

$(tim): Alphabet.hs Catalogue.hs Comparison.hs Context.hs Derivative.hs Expression.hs \
Function.hs Fuse.hs Generator.hs Info.hs List.hs OK.hs PreOrderTrees.hs \
Pressing.hs Queue.hs StarPromotion.hs Stellation.hs \
SyntaxCatalogue.hs Tim.hs Parameters.hs OneLetterFactorization.hs \
popproxy.txt semproxy.txt synproxy.txt
	ghc -O Tim

runTimes.pdf: runTimes.tex runTimesTables.tex
	pdflatex runTimes.tex

runTimesTables.tex: $(runtimes) $(timscript) $(mrE) popproxy.txt timproxy.txt
ifndef OS
	./RunTimes > runTimesTables.tex
else
	RunTimes.exe > runTimesTables.tex
endif

effectDataTables.tex: effproxy.txt $(effect) $(effscript) $(effdata) popproxy.txt
ifndef OS
	./EffectData > effectDataTables.tex
else
	EffectData.exe > effectDataTables.tex
endif

$(effdata): EffectData.hs ReadTable.hs
	ghc -O EffectData.hs

$(runtimes): RunTimes.hs ReadTable.hs
	ghc -O RunTimes.hs

sizeRatios.pdf: sizeRatios.tex sizeRatiosTables.tex
	pdflatex sizeRatios.tex

sizeRatiosTables.tex: sizeRatios $(mrE) popproxy.txt
	./sizeRatios > sizeRatiosTables.tex

$(test): List.hs Expression.hs Info.hs Catalogue.hs Context.hs Comparison.hs Fuse.hs \
Parameters.hs Pressing.hs Stellation.hs StarPromotion.hs SyntaxCatalogue.hs \
Test.hs
	ghc -O Test

$(minratios): Alphabet.hs AutIntersect.hs Catalogue.hs Comparison.hs Context.hs \
Derivative.hs Expression.hs Function.hs Fuse.hs Generator.hs GruberP.hs Info.hs List.hs \
MinRatios.hs Museum.hs OK.hs OneLetterFactorization.hs Parameters.hs Parser.hs \
PreOrderTrees.hs Pressing.hs Queue.hs StarPromotion.hs Stellation.hs SyntaxCatalogue.hs
	ghc -O MinRatios
