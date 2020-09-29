# sources of all Haskell modules apart from Main programs

haskellmodules = Alphabet.hs AutIntersect.hs BigNum.hs Catalogue.hs \
 Comparison.hs Context.hs Derivative.hs Expression.hs Function.hs \
 Fuse.hs Generator.hs GruberP.hs Info.hs List.hs Museum.hs OK.hs \
 OneLetterFactorization.hs Parameters.hs Parser.hs PreOrderTrees.hs \
 Pressing.hs Queue.hs RegexpCount.hs StarPromotion.hs Stellation.hs \
 SyntaxCatalogue.hs TrafoLimits.hs

# compiling Haskell programs

ifndef OS
comparetrafo=CompareTrafo
createexps=CreateAllExps
createpops=CreateAllPops
createsem=CreateSemCatalogue
createsyn=CreateSynCatalogue
exptest=ExpTest
huextract=HUExtract
mrE=MrE
poptest=PopTest
reg=Reg
runallexptests=RunAllExpTests
runallpoptests=RunAllPopTests
test=Test
tabulate=Tabulate
else
comparetrafo=CompareTrafo.exe
createexps=CreateAllExps.exe
createpops=CreateAllPops.exe
createsem=CreateSemCatalogue.exe
createsyn=CreateSynCatalogue.exe
exptest=ExpTest.exe
huextract=HUExtract.exe
mrE=MrE.exe
poptest=PopTest.exe
reg=Reg.exe
runallexptests=RunAllExpTests.exe
runallpoptests=RunAllPopTests.exe
test=Test.exe
tabulate=Tabulate.exe
endif

compiledprogs = $(comparetrafo) $(createexps) $(createpops) $(createsem) $(createsyn) \
$(exptest) $(huextract) $(mrE) $(poptest) $(reg) $(runallexptests) $(runallpoptests) \
$(tabulate) $(test)

# the simplification program itself is MrE
# it may need to look expressions up in catalogues

simplifier: $(mrE) catalogues

GHC = ghc --make -O

$(comparetrafo): CompareTrafo.hs $(haskellmodules)
	$(GHC) CompareTrafo.hs

$(createexps): CreateAllExps.hs $(haskellmodules)
	$(GHC) CreateAllExps.hs

$(createpops): CreateAllPops.hs $(haskellmodules)
	$(GHC) CreateAllPops.hs

$(createsem): CreateSemCatalogue.hs $(haskellmodules)
	$(GHC) CreateSemCatalogue.hs

$(createsyn): CreateSynCatalogue.hs $(haskellmodules)
	$(GHC) CreateSynCatalogue.hs

$(exptest): ExpTest.hs $(haskellmodules)
	$(GHC) ExpTest.hs

$(huextract): HUExtract.hs $(haskellmodules)
	$(GHC) HUExtract.hs

$(mrE): MrE.hs $(haskellmodules)
	$(GHC) MrE.hs

$(poptest): PopTest.hs $(haskellmodules)
	$(GHC) PopTest.hs

$(reg): Reg.hs $(haskellmodules)
	$(GHC) Reg.hs

$(runallexptests): RunAllExpTests.hs $(haskellmodules)
	$(GHC) RunAllExpTests.hs

$(runallpoptests): RunAllPopTests.hs $(haskellmodules)
	$(GHC) RunAllPopTests.hs

$(tabulate): Tabulate.hs $(haskellmodules)
	$(GHC) Tabulate.hs

$(test): Test.hs $(haskellmodules)
	$(GHC) Test.hs

# creating catalogues of small minimal regular expressions
# with textual proxies for catalogue directories

catalogues: synproxy.txt semproxy.txt

semproxy.txt: $(createsem) synproxy.txt
ifndef OS
	./CreateSemCatalogue
else
	CreateSemCatalogue.exe
endif
	echo semcat > semproxy.txt

synproxy.txt: $(createsyn)
ifndef OS
	./CreateSynCatalogue
else
	CreateSynCatalogue.exe
endif
	echo syncat > synproxy.txt

# generating test data

testdata: popproxy.txt expproxy.txt

popproxy.txt: $(reg) $(createpops)
ifndef OS
	./CreateAllPops
else
	CreateAllPops.exe
endif
	echo population > popproxy.txt

expproxy.txt: $(huextract) $(createexps)
ifndef OS
	./CreateAllExps
else
	CreateAllExps.exe
endif
	echo expansion > expproxy.txt

# running tests and processing results

correctnesscheck: $(test)
ifndef OS
	./Test 100000
else
	Test.exe 100000
endif

results: TestResults.pdf

TestResults.pdf: TestResults.tex \
effectsTables.tex runTimesTables.tex HUeffectsTables.tex minRatiosTables.tex
	pdflatex TestResults.tex

effectsTables.tex: $(tabulate) popresproxy.txt
ifndef OS
	./Tabulate popresults "input expressions of size" "Mean percentages output-size / input-size" 1 1.0 > effectsTables.tex
else
	Tabulate.exe popresults "input expressions of size" "Mean percentages output-size / input-size" 1 1.0 > effectsTables.tex
endif

runTimesTables.tex: $(tabulate) popresproxy.txt
ifndef OS
	./Tabulate popresults "input expressions of size" "Average simplification times (ms)" 0 1000.0 > runTimesTables.tex
else
	Tabulate.exe popresults "input expressions of size" "Average simplification times (ms)" 0 1000.0 > runTimesTables.tex
endif

HUeffectsTables.tex: $(tabulate) expresproxy.txt
ifndef OS
	./Tabulate expresults "minimal size" "Mean percentages (output size / input size)" 0 1.0 > HUeffectsTables.tex
else
	Tabulate.exe expresults "minimal size" "Mean percentages (output size / input size)" 0 1.0 > HUeffectsTables.tex
endif

minRatiosTables.tex: $(tabulate) expresproxy.txt
ifndef OS
	./Tabulate expresults "minimal size" "Mean (output size / minimal size)" 1 1.0 > MinRatiosTables.tex
else
	Tabulate.exe expresults "minimal size" "Mean (output size / minimal size)" 1 1.0 > MinRatiosTables.tex
endif

popresproxy.txt: $(poptest) $(runallpoptests) popproxy.txt semproxy.txt synproxy.txt
ifndef OS
	./RunAllPopTests
else
	RunAllPopTests.exe
endif
	echo popres > popresproxy.txt

expresproxy.txt: $(exptest) $(runallexptests) expproxy.txt semproxy.txt synproxy.txt
ifndef OS
	./RunAllExpTests
else
	RunAllExpTests.exe
endif
	echo expres > expresproxy.txt

# removing all files derived from repository sources (see .gitignore)

clean:
	rm *.hi *.o
	rm $(compiledprogs)
	rm -rf semcatalogue syncatalogue
	rm -rf populations expansions
	rm -rf popresults* expresults*
	rm *Tables*.tex
	rm *.aux *.log *.pdf
	rm *proxy.txt

# --------------------------------------------------------------------
# variant rules for tests with final transformation unlimited by
# expression size

popresproxy-u.txt: $(poptest) $(runallpoptests) popproxy.txt semproxy.txt synproxy.txt
ifndef OS
	./RunAllPopTests 100 -u
else
	RunAllPopTests.cmd 100 -u
endif
	echo popres > popresproxy-u.txt
# & similarly for expresproxy-u.txt

runTimesTablesU.tex: $(tabulate) popresproxy-u.txt
ifndef OS
	./Tabulate popresults-u "for expressions of size" "Unlimited simplification times" 0 1000.0 > runTimesTablesU.tex
else
	Tabulate.exe popresults-u "for expressions of size" "Unlimited simplification times" 0 1000.0 > runTimesTablesU.tex
endif
# & similarly for effectsTablesU.tex, HUeffectsTablesU.tex & minRatiosTablesU.tex
