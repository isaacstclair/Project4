
#include "Interpreter.h"

Interpreter::Interpreter(DatalogProgram datalog, Database database){
    this->datalog = datalog;
    this->database = database;
}

Interpreter::~Interpreter() {
    VectorSeenBefore.clear();
    VectorToProject.clear();
}

Relation Interpreter::EvaluatePredicate(Predicate p){
    std::string name = p.GetName();
    Header header = Header(p.GetParameters());
    Relation relation = Relation(name, header);
    return(relation);
}

std::vector<Relation> Interpreter::EvaluatePredicates(std::vector<Predicate> p){
    std::vector<Relation> relationVector;
    std::set<Tuple> tuples;
    for(int i=0; i<int(p.size()); i++){
        std::string name = p.at(i).GetName();
        Header header = Header(p.at(i).GetParameters());
        Relation relation = Relation(name, header);
        tuples = database.GetRelation(database.GetRelationIndex(name)).GetTuples();
        for(Tuple t : tuples){
            relation.AddTuple(t);
        }

        relationVector.push_back(relation);
    }
    return relationVector;
}

bool Interpreter::CheckDuplicate(Parameter par){
    for(int i=0; i < int(VectorSeenBefore.size()); i++){
        if(VectorSeenBefore.at(i) == par.GetParameter()){
            return true;
        }
    }
    return false;
}

int Interpreter::GetFirstInstance(Parameter par){

    for(int i=0; i < int(VectorSeenBefore.size()); i++){
        if(VectorSeenBefore.at(i) == par.GetParameter()){
            return(i);
        }
    }
    return(-1);
}

void Interpreter::EvaluateSchemes(){
    for(int i=0; i < int(datalog.SchemesPredicates.size()); i++){
        Relation relation = EvaluatePredicate(datalog.SchemesPredicates.at(i));
        database.AddRelation(relation);
    }
}

void Interpreter::EvaluateFacts(){
    for(int i=0; i < int(datalog.FactsPredicates.size()); i++){
        std::string name = datalog.FactsPredicates.at(i).GetName();
        std::vector<std::string> values = datalog.FactsPredicates.at(i).GetParameters();
        database.AddFact(name, values);
    }
}

void Interpreter::EvaluateRules() {
    std::vector<Relation> bodyRelations;
    std::vector<Relation> finishedRelations;
    std::cout << "Rule Evaluation" << std::endl;
    bool print;
    bool again = false;
    int sum;
    int ruleNum=0;
    do{
        sum = 0;
        for (int i = 0; i < int(datalog.Rules.size()); i++) {
            Predicate head = datalog.Rules.at(i).GetHeadPredicates();
            std::string finalName = datalog.Rules.at(i).GetHeadPredicates().GetName();
            std::vector<Predicate> body = datalog.Rules.at(i).GetBodyPredicates();
            bodyRelations = EvaluatePredicates(body);

            for (int j = 0; j < int(bodyRelations.size()); j++) {
                VectorSeenBefore.clear();
                VectorToProject.clear();
                std::vector<std::string> parameters = bodyRelations.at(j).GetParameters();

                for (int k = 0; k < int(parameters.size()); k++) {
                    //if is a string
                    if (parameters.at(k).at(0) == '\'') {
                        bodyRelations.at(j) = bodyRelations.at(j).Select(k, parameters.at(k));
                    } else if (CheckDuplicate(parameters.at(k))) {
                        bodyRelations.at(j) = bodyRelations.at(j).Select(GetFirstInstance(parameters.at(k)), k);
                    } else if (!CheckDuplicate(parameters.at(k))) {
                        VectorSeenBefore.push_back(parameters.at(k));
                        VectorToProject.push_back(k);
                    }
                }

                bodyRelations.at(j) = bodyRelations.at(j).Project(VectorToProject);
                bodyRelations.at(j) = bodyRelations.at(j).Rename(VectorSeenBefore);

            }


            int counter = 1;
            do {
                if (bodyRelations.size() > 1) {
                    bodyRelations.at(0) = bodyRelations.at(0).Join(bodyRelations.at(counter));
                    counter++;
                }
            } while (counter < int(bodyRelations.size()));


            Relation relation = bodyRelations.at(0);
            std::vector<int> toProject;
            for (int j = 0; j < int(head.GetParameters().size()); j++) {
                for (int k = 0; k < relation.GetHeader().Size(); k++) {
                    if (relation.GetHeader().GetAttribute(k) == head.GetParameters().at(j)) {
                        toProject.push_back(k);
                    }
                }
            }
            relation = relation.ProjectSecond(toProject);
            relation.SetName(finalName);

            //Time to turn this into a string

            std::cout << datalog.Rules.at(i).RuleToString() << "." << std::endl;
            for (Tuple t : relation.GetTuples()) {
                print = database.Unionize(relation.GetName(), t);
                if (print) {
                    Header updatedHeader = database.FindNewHead(relation.GetName());
                    sum++;
                    for(int j=0; j<updatedHeader.Size(); j++){
                        if(j != updatedHeader.Size()-1){
                            std::cout << "  " << updatedHeader.GetAttribute(j) << "=" << t.GetValue(j) << ", ";
                        } else{
                            std::cout << updatedHeader.GetAttribute(j) << "=" << t.GetValue(j) << std::endl;
                        }

                    }


                }
            }
        }
        ruleNum++;
        if(sum==0){
            break;
        }
    }while(sum != 0);


    std::cout << std::endl << "Schemes populated after " << ruleNum << " passes through the Rules." << std::endl << std::endl;

}


void Interpreter::EvaluateQueries(){

    std::cout << "Query Evaluation" << std::endl;
    for(int i=0; i < int(datalog.QueriesPredicates.size()); i++){

        VectorSeenBefore.clear();
        VectorToProject.clear();

        std::string name = datalog.QueriesPredicates.at(i).GetName();
        int pos = database.GetRelationIndex(name);
        Relation relation = database.GetRelation(pos);
        std::vector<std::string> parameters = datalog.QueriesPredicates.at(i).GetParameters();


        for(int j=0; j < int(parameters.size()); j++) {
            //if is a string
            if (parameters.at(j).at(0) == '\'') {
                relation = relation.Select(j, parameters.at(j));
            } else if (CheckDuplicate(parameters.at(j))) {
                relation = relation.Select(GetFirstInstance(parameters.at(j)),j);
            } else if (!CheckDuplicate(parameters.at(j))) {
                VectorSeenBefore.push_back(parameters.at(j));
                VectorToProject.push_back(j);
            }
        }

        relation = relation.Project(VectorToProject);
        relation = relation.Rename(VectorSeenBefore);

        bool allStrings = QueryCheck(datalog.QueriesPredicates.at(i).GetParameters());

        if(relation.GetTupleSize() > 0){ //&& !allStrings){
            std::cout << datalog.QueriesPredicates.at(i).QueryToString() << " Yes(" << relation.GetTupleSize() << ")" << std::endl;
            relation.RelationToString();
        } else if(relation.GetTupleSize() > 0 && allStrings){
            std::cout << datalog.QueriesPredicates.at(i).QueryToString() << " Yes(" << relation.GetTupleSize() << ")" << std::endl;
        } else{
            std::cout << datalog.QueriesPredicates.at(i).QueryToString() << " No" << std::endl;
            relation.RelationToString();
        }
    }
}

void Interpreter::Interpret(){



    EvaluateSchemes();

    EvaluateFacts();

    EvaluateRules();

    EvaluateQueries();


}


bool Interpreter::QueryCheck(std::vector<std::string> parameters){
    int sum = 0;
    for(int i=0; i < int(parameters.size()); i++){
        if(parameters.at(i)[0] == '\''){
            sum++;
        }
    }
    if(sum == int(parameters.size())){
        return true;
    } else{
        return false;
    }
}





