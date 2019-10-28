#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>
#include <map>

class Rule {
 public:
 char head;
 std::vector<char> positiveBody;
 std::vector<char> negativeBody;

 Rule(char firstOfRule) {
  this->head = firstOfRule;
 }

 void addPosBody(std::string body) {
  std::vector<char>::iterator it;
  int bodyLength = body.length();
  if(body.empty()) {
   return;
  }
  for(int i = 0; i < bodyLength; ++i) {
   this->positiveBody.push_back(body[i]);
  }
 }
 
 void addNegBody(std::string body) {
  std::vector<char>::iterator it;
  int bodyLength = body.length();
  if(body.empty()) {
   return;
  }
  for(int i = 0; i < bodyLength; ++i) {
   this->negativeBody.push_back(body[i]);
  }
 }

 bool emptyBody() {
  return (this->positiveBody.empty() && this->negativeBody.empty());
 }
 
 bool consequence(std::map<char, int> posConsequence, std::map<char, int> negConsequence) {
  int sizeOfPos = this->sizeOfPos(), sizeOfNeg = this->sizeOfNeg();
  bool retVal = true;
  if(!this->positiveBody.empty()) {
   for(int i = 0; i < sizeOfPos; i++) {
    if(posConsequence.find(this->positiveBody[i]) == posConsequence.end()) {
     retVal = false;
    }
   }
  }
  if(!this->negativeBody.empty()) {
   for(int i = 0; i < sizeOfNeg; i++) {
    if(negConsequence.find(this->negativeBody[i]) == negConsequence.end()) {
     retVal = false;
    }
   }
  }
  return retVal;
 }
 
 bool intersectionPos(std::map<char, int> consequence) {
  int sizeOfPosBody = this->sizeOfPos();
  for(int i = 0; i < sizeOfPosBody; i++) {
   if(consequence.find(this->positiveBody[i]) != consequence.end()) {
    return true;
   }
  }
 return false;
 }

 bool intersectionNeg(std::map<char, int> consequence) {
  int sizeOfNegBody = this->sizeOfNeg();
  for(int i = 0; i < sizeOfNegBody; i++) {
   if(consequence.find(this->negativeBody[i]) != consequence.end()) {
    return true;
   }
  }
 return false;
 }

 int sizeOfPos(){
  return this->positiveBody.size();
 }

 int sizeOfNeg(){
  return this->negativeBody.size();
 }

 bool operator == (const Rule &rule1) {
  return this->head == rule1.head;
 }
};

void forwardChain(std::vector<Rule> kB) {
 int sizeOfKb = kB.size();
 std::map <char, int> allPossibleConsequences;
 std::map<char, int> posConsequences, negConsequences;

 for(int i = 0; i < sizeOfKb; ++i) {
  if(kB[i].emptyBody()) {
   posConsequences[kB[i].head] = 1;
   std::cout << "Derived literal: " << kB[i].head << " because there is no body for this rule\n";
  }
  allPossibleConsequences[kB[i].head]++;
 }
 for(int i = 0; i < sizeOfKb; ++i) {
  int sizeOfPosBody = kB[i].sizeOfPos(), sizeOfNegBody = kB[i].sizeOfNeg();
  for(int j = 0; j < sizeOfPosBody; j++) {
   if(allPossibleConsequences.find(kB[i].positiveBody[j]) == allPossibleConsequences.end()) {
    negConsequences[kB[i].positiveBody[j]] = 1;
    allPossibleConsequences[kB[i].positiveBody[j]]++;
    std::cout << "Derived literal: ~" << kB[i].positiveBody[j] << " because this literal does not exist as a head in any other rule\n";
   }
  }
  for(int j = 0; j < sizeOfNegBody; j++) {
   if(allPossibleConsequences.find(kB[i].negativeBody[j]) == allPossibleConsequences.end()) {
    negConsequences[kB[i].negativeBody[j]] = 1;
    allPossibleConsequences[kB[i].negativeBody[j]]++;
    std::cout << "Derived literal: ~" << kB[i].negativeBody[j] << " because this literal does not exist as a head in any other rule\n";
   }
  }
 }
 bool noChanges = true;
 int index = 0, iterationsWithNoChange = 0;
 while(noChanges == true && iterationsWithNoChange != sizeOfKb) { 
  if(kB[index].consequence(posConsequences, negConsequences) && (posConsequences.find(kB[index].head) == posConsequences.end() && negConsequences.find(kB[index].head) == negConsequences.end())) {
   posConsequences[kB[index].head] = 1;
   std::cout << "Derived literal: " << kB[index].head << " because this literal has a body that matches all the literals previously derived\n";
   noChanges = false;
  } else if (posConsequences.find(kB[index].head) == posConsequences.end() && negConsequences.find(kB[index].head) == negConsequences.end()) {
   if(allPossibleConsequences[kB[index].head] > 1) {
    bool negatable = true;
    std::vector<bool> negationIntersectAllRules;
    for(int i = 0; i < sizeOfKb; i++) {
     if(kB[i] == kB[index]) {
      negationIntersectAllRules.push_back(kB[i].intersectionNeg(posConsequences));
      negationIntersectAllRules.push_back(kB[i].intersectionPos(negConsequences));
     }
    }
    int sizeOfAllNegation = negationIntersectAllRules.size();
    for(int i = 0; i < sizeOfAllNegation; i+=2) {
     if(!negationIntersectAllRules[i] && !negationIntersectAllRules[i + 1]) {
      negatable = false;
     }
    }
    if(negatable) {
     negConsequences[kB[index].head] = 1;
     std::cout << "Derived literal: ~" << kB[index].head << " because the rule had an intersect with some negative consequences derived\n";
     noChanges = false;
    }
   } else {
    bool posConsIntersectNegBody = kB[index].intersectionNeg(posConsequences);
    bool negConsIntersectPosBody = kB[index].intersectionPos(negConsequences);
    if(posConsIntersectNegBody || negConsIntersectPosBody) {
     negConsequences[kB[index].head] = 1;
     std::cout << "Derived literal: ~" << kB[index].head << " because the rule had an intersect with some negative consequences derived\n";
     noChanges = false;
    }
   }
  }
  if(iterationsWithNoChange == sizeOfKb - 1) {
   break;
  } else if(noChanges == false && index == sizeOfKb - 1) {
   iterationsWithNoChange = 0;
   noChanges = true;
   index = 0;
  } else if (noChanges == true && index == sizeOfKb - 1) {
   iterationsWithNoChange++;
   index = 0;
  } else if(index < sizeOfKb - 1) {
   if(noChanges == false) {
    noChanges = true;
    iterationsWithNoChange = 0;
   } else {
    iterationsWithNoChange++;
   }
   index++;
  }
 }
 std::cout << "The positive consequences are: ";
 std::map<char, int>::iterator itPos, itNeg, itPosEnd = std::prev(posConsequences.end(), 1), itNegEnd = std::prev(negConsequences.end(), 1);
 for(itPos = posConsequences.begin(); itPos != posConsequences.end(); ++itPos) {
  if(itPos == itPosEnd) {
   std::cout << itPos->first << "\n";
  } else {
   std::cout << itPos->first << ", ";
  }
 }
 std::cout << "And the negative consequences are: ";
 for(itNeg = negConsequences.begin(); itNeg != negConsequences.end(); ++itNeg) {
  if(itNeg == itNegEnd) {
   std::cout << "~" << itNeg->first << "\n";
  } else {
   std::cout << "~" << itNeg->first << ", ";
  } 
 }
}

int main(int argc, char* argv[]) {
 std::string currentLine;
 std::ifstream file(argv[1]);
 std::vector<Rule> knowledgeBase;
 if(!file) { std::cout << "Bad file input\n"; return 1;}
 while(std::getline(file, currentLine)) {
  int stringSize = currentLine.length();
  if(currentLine[0] != '#') {
   std::string::iterator end_pos = std::remove(currentLine.begin(), currentLine.end(), ' ');
   currentLine.erase(end_pos, currentLine.end());
   Rule newRule(currentLine[1]);
   int posBody = currentLine.find('[', 1);
   int posBodyEnd = currentLine.find(']', posBody);
   int posBodyLength = posBodyEnd - posBody - 1;
   std::string posBodyString = currentLine.substr(posBody + 1, posBodyLength);
   int negBody = currentLine.find('[', posBodyEnd);
   int negBodyEnd = currentLine.find(']', negBody);
   int negBodyLength = negBodyEnd - negBody - 1;
   std::string negBodyString = currentLine.substr(negBody + 1, negBodyLength);
   newRule.addPosBody(posBodyString);
   newRule.addNegBody(negBodyString);
   knowledgeBase.push_back(newRule);
  }
 }
 file.close();
 forwardChain(knowledgeBase);
 return 0;
}
