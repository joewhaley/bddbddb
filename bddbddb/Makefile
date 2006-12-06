MODULES = net
SUPPORT_LIBS = javabdd-2.0.jar jwutil-1.0.jar weka.jar jdom.jar
JAR_NAME = bddbddb.jar
FULL_JAR_NAME = bddbddb-full.jar

ifeq (${OS},Windows_NT)
  CLASSPATH_SEP = \;
  BUILD_CLASSPATH = ".;$(subst $(space),;,$(SUPPORT_LIBS))"
  JDK_ROOT = $(firstword $(wildcard c:/j2sdk*))
else
  CLASSPATH_SEP = :
  BUILD_CLASSPATH = .:$(subst $(space),:,$(SUPPORT_LIBS))
  JDK_ROOT = $(firstword $(wildcard /usr/java/j2sdk*))
endif

# The java tools:
JAVA = $(JDK_ROOT)/bin/java
JAVAC = $(JDK_ROOT)/bin/javac
JAVADOC = $(JDK_ROOT)/bin/javadoc
JAR = $(JDK_ROOT)/bin/jar
JIKES = jikes

ALLDIRS := $(shell find $(MODULES) -type d | grep -v CVS)
ALLJAVA := $(foreach d, $(ALLDIRS), $(wildcard $(d)/*.java))
ALLPKGS := $(sort $(foreach j, $(shell echo $(ALLJAVA) | sed 's/\.\.\/[^\/]*\///g'), $(patsubst %/,%,$(dir $(j)))))
ALLPKGNAMES := $(subst /,.,$(ALLPKGS))

CLASSFILE_VERSION = 1.3

all:	jar

### RULES TO BUILD SOURCE CODE
#
jikes:	source_list _jikes
# _jikes: Assumes prior existence of the .source_list file.
# Useful on cygwin, because cygwin takes a long time to build the .source_list file.
_jikes:	
	$(JIKES) -target $(CLASSFILE_VERSION) -classpath $(BUILD_CLASSPATH) @.source_list

jikes-pedantic:	source_list
	$(JIKES) -target $(CLASSFILE_VERSION) -classpath $(BUILD_CLASSPATH) +P @.source_list

javac:	source_list _javac
# _javac: Assumes prior existence of the .source_list file.
# Useful on cygwin, because cygwin takes a long time to build the .source_list file.
_javac:	
	$(JAVAC) -g -source $(CLASSFILE_VERSION) -target $(CLASSFILE_VERSION) -classpath $(BUILD_CLASSPATH) @.source_list


### RULES TO CLEAN
#
clean:
	find $(MODULES) -name "*.class" | xargs rm -f $(JAR_NAME) $(FULL_JAR_NAME)

veryclean:
	find $(MODULES) -name "*.class" | xargs rm -f $(JAR_NAME) $(FULL_JAR_NAME) .source_list .class_list


### RULES TO ACCESS CVS
#
update:
	( export CVS_RSH=ssh ; cvs update -Pd )

commit:
	( export CVS_RSH=ssh ; cvs commit )


### RULES FOR BUILDING JAVADOC
#
javadoc: $(ALLJAVA)
	$(JAVADOC) -classpath $(BUILD_CLASSPATH) -breakiterator -d javadoc $(ALLPKGNAMES)


### RULES TO BUILD JAR
#
jar: $(JAR_NAME)

$(JAR_NAME): class_list
	$(JAR) cfm $(JAR_NAME) bddbddbManifest @.class_list

fulljar: $(JAR_NAME) $(SUPPORT_LIBS) bddbddb.pro
	java -jar proguard.jar @bddbddb.pro

### RULES TO RUN TEST CASES
#
DATALOG = ../bddbddb_examples/pa.datalog
test:	net/sf/bddbddb/Solver.class
	$(JAVA) -mx512m -cp $(BUILD_CLASSPATH) $(TESTOPT) net.sf.bddbddb.Solver $(DATALOG)

interactive:	net/sf/bddbddb/Interactive.class
	$(JAVA) -mx512m -cp $(BUILD_CLASSPATH) $(TESTOPT) net.sf.bddbddb.Interactive $(DATALOG)


### MISC RULES
#
wc:
	@echo Total, and Top Five files:
	@wc -l $(ALLJAVA) | sort -rn | head -7


### LOCAL RULES (you will never need to make these directly)
#
source_list:
	@echo Building source list...
	@echo $(ALLJAVA) | xargs -n 1 echo > .source_list
#	@find $(MODULES) -name "*.java" > .source_list

class_list: javac
	@echo Building class list...
	@find $(MODULES) -name "*.class" > .class_list

%.class: %.java #javac
	$(JAVAC) -g -source $(CLASSFILE_VERSION) -target $(CLASSFILE_VERSION) -classpath $(BUILD_CLASSPATH) $<

empty:=
space:=$(empty) $(empty)
