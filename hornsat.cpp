#include <iostream>
#include <fstream>
#include <vector>
#include <sstream>
#include <iterator>

using namespace std;

void print_entrada(const vector< vector<int> >& entrada)
{
    cout << " [entrada]"<< endl;
    for(unsigned i=0;i<entrada.size();i++)
    {
        cout << "  ";
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            cout << entrada[i][j] << "   ";
        }
        cout<<endl;
    }
    cout << " ---------"<< endl<<endl;
}

pair<int, int> get_fact(const vector< vector<int> >& entrada)
{
    // Guarda os indices da clausula unitaria encontrada para ser retornada pela função
    int index_L{-1}, index_C{-1};

    // Procurar a clausula unitaria
    for(unsigned i=0;i<entrada.size();i++)
    {
        int cont{0};
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            if(entrada[i][j] != 0)
            {
                index_L = i;
                index_C = j;
                cont++;
            }
        }
        if(cont == 1)
        {
            if(entrada[index_L][index_C] > 0)
            {
                // Retorno da primeira clausula unitária encontrada
                return pair<int, int>{index_L, index_C};
            }
        }
    }

    // Retorno pra quando o laço nao achar clausulas unitarias
    return pair<int, int>{-1, -1};
}


void result(bool res)
{
    if(res){ cout << " Resultado: [satisfazivel]\n\n";   }
    else   { cout << " Resultado: [insatisfazivel]\n\n"; exit(0); }
}


bool empty_input(const std::vector< std::vector<int> >& entrada)
{
    int cont{0};
    // Chacar se a estrutura está vazia
    for(unsigned i=0;i<entrada.size();i++)
    {
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            if(entrada[i][j] != 0)
            {
                cont++;
            }
        }
    }

    if(cont == 0){ return true; }
    return false;
}


bool has_one_fact(const std::vector< std::vector<int> >& entrada)
{
    int cont{0};
    for(unsigned i=0;i<entrada.size();i++)
    {
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            if(entrada[i][j] > 0)
            {
                cont++;
            }
        }
    }
    if(cont == 1)
    {
        return true;
    }

    return false;
}

std::vector< std::pair<int, int> > simplifica(std::vector< std::vector<int> >& entrada)
{
    // verificar se exxistem clausulas já vazias
    for(unsigned i=0;i<entrada.size();i++)
    {
        if(entrada[i].size() == 0)
        {
            //std::cout << "??? " <<
            result(false);
            return std::vector< std::pair<int, int> >();
        }
    }

    std::vector< pair<int, int> > facts_arr;
    for(;;)
    {
        // Procurar primeiro fato e retornar os indices;
        auto fact_index = get_fact(entrada);

        // se <claus_unit_index> tiver indices de valor -1, significa que nao existe mais nenhum fato.
        if(fact_index.first == -1 && fact_index.second == -1){ return facts_arr; }
        if(empty_input(entrada)) { return facts_arr; }

        // Verificar se existe apenas 1 clausula unitaria em toda a estrutura
        ///if(has_one_fact(entrada)){ /*result(true);*/ return; }

        // Guardar a clausula unitaria
        int fact = entrada[fact_index.first][fact_index.second];

        // Eliminar toda linha que contem uma clausula unitaria
        for(unsigned i=0; i<entrada.size(); i++)
        {
            for(unsigned j=0;j<entrada[i].size();j++)
            {
                if(entrada[i][j] == fact)
                {
                    for(unsigned k=0; k<entrada[i].size(); k++)
                    {
                        entrada[i][k] = 0;
                    }
                }
            }
        }

        // Eliminar os valores opostos da clausila unitaria
        for(unsigned i=0; i<entrada.size(); i++)
        {
            for(unsigned j=0; j<entrada[i].size(); j++)
            {
                if(entrada[i][j] == (fact * (-1)))
                {
                    entrada[i][j] = 0;
                }
            }
        }

        facts_arr.push_back(fact_index);
    }

    return facts_arr;
}


bool check_valid(const vector< vector<int> >& entrada)
{
    int cont{0};
    // Chacar se a estrutura está vazia
    for(unsigned i=0;i<entrada.size();i++)
    {
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            if(entrada[i][j] != 0)
            {
                cont++;
            }
        }
    }

    if(cont==0)
    {
      result(false);
      return false;
    }
    else
    {
        result(true);
        return true;
    }
}


void print_valoration(const vector< vector<string> >& entrada)
{
    // imprimir a formula
    for(unsigned i=0;i<entrada.size();i++)
    {
        cout << " (";
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            cout << entrada[i][j] << (j==entrada[i].size()-1 ? "" : "#");

        }
        cout << ") ";
        cout << (i==entrada.size()-1 ? "" : "&");
    }
    cout<<endl;
}

void show_valoration(const vector< vector<int> >& entrada)
{
    cout << " Valoração: \n";
    //print_valoration(entrada);

    // transformar a estrutura em array de strings para representar o (-0)
    vector< vector<string> > entrada_str;
    for(unsigned i=0;i<entrada.size();i++)
    {
        vector<string> buffer;
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            stringstream ss;
            ss << entrada[i][j];
            string str = ss.str();
            buffer.push_back(str);
        }
        entrada_str.push_back(buffer);
    }

    print_valoration(entrada_str);

    // capturar is indices dos fatos existentes na formula
    vector< pair<int, int> > facts_index;
    for(unsigned i=0;i<entrada.size();i++)
    {
        if(entrada[i].size() == 1) // clausula unitária
        {
            if(entrada[i][0] > 0) // é positivo; FATO
            {
                facts_index.push_back( pair<int, int>{i, 0});
            }
        }
    }

    vector< pair<int, int> > facts_cl_POS_index;
    // procurar indice dos fatos em outras clausulas (valores POSITIVOS)
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
            for(auto& fact : facts_index)
            {
                if(entrada_str[fact.first][fact.second] == entrada_str[i][j])
                {
                    facts_cl_POS_index.push_back(pair<int, int>{i, j});
                }
            }

        }
    }

    vector< pair<int, int> > facts_cl_NEG_index;
    // procurar indice dos fatos em outras clausulas (valores NEGATIVOS)
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
            for(auto& fact : facts_index)
            {
                if(("-" + entrada_str[fact.first][fact.second]) == entrada_str[i][j])
                {
                    facts_cl_NEG_index.push_back(pair<int, int>{i, j});
                }
            }

        }
    }

    // colocar 0 em tudo e manter o sinal
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
            if(entrada_str[i][j].size() == 1)
            {
                entrada_str[i][j] = "0";
            } else
            {
                entrada_str[i][j] = "-0";
            }
        }

    }

    // colocar 1 em todos os fatos
    for(unsigned i=0;i<facts_index.size();i++)
    {
        entrada_str[facts_index[i].first][facts_index[i].second] = "1";
    }

    // colocar 1 em todos os fatos POSITIVOS
    for(unsigned i=0;i<facts_cl_POS_index.size();i++)
    {
        entrada_str[facts_cl_POS_index[i].first][facts_cl_POS_index[i].second] = "1";
    }

    // colocar 1 em todos os fatos NEGATIVOS
    for(unsigned i=0;i<facts_cl_NEG_index.size();i++)
    {
        entrada_str[facts_cl_NEG_index[i].first][facts_cl_NEG_index[i].second] = "-1";
    }

    print_valoration(entrada_str);

    // resolver as negações
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
           if(entrada_str[i][j] == "-1"){ entrada_str[i][j] = "0"; } else
           if(entrada_str[i][j] == "-0"){ entrada_str[i][j] = "1"; }
        }

    }

    print_valoration(entrada_str);

    // simplificar 01
    vector<int> entrada_str_simpl_1;
    for(unsigned i=0;i<entrada_str.size();i++)
    {
        bool sum = 0;
        for(unsigned j=0;j<entrada_str[i].size();j++)
        {
            if(entrada_str[i][j] == "1"){ sum += 1; }
        }

        entrada_str_simpl_1.push_back(sum);
    }

    bool result = true;

    cout << " (";
    for(unsigned i=0;i<entrada_str_simpl_1.size();i++)
    {
        cout << (entrada_str_simpl_1[i]>0) <<  (i==entrada.size()-1 ? "" : " & ");
        if(entrada_str_simpl_1[i]==0){result = false; }
    }
    cout << ")\n";

    cout << " (" << result << ")";

    puts("\n");
}


vector< vector<int> > openfile(string path)
{
    FILE* file = fopen(path.c_str(), "r");
    stringstream file_content;

    puts("");
    int j = 0;
    while((j = fgetc(file)) != EOF)
    {
        file_content << (char)j;
    }

    fclose(file);

    vector< vector<int> > entrada;

    int val = 0;
    int c = 0;
    int sig = 1;
    vector<int> buffer;
    for(unsigned i=0;i<file_content.str().size();i++)
    {

        if(file_content.str()[i] == '-') { sig = -1; }
        if(isdigit(file_content.str()[i]))
        {
            do
            {
                c = file_content.str()[i];
                if(!isdigit(c)){ break; }
                else { val = val*10 + (c-48); }
                i++;
            }
            while(val>=0);
            buffer.push_back(val * sig);
            sig = 1;
        }

        if(file_content.str()[i] == '\n' || file_content.str()[i] == '\r'){
            entrada.push_back(buffer);
            buffer.clear();
        }

        val = 0;
    }

    return entrada;
}


bool check_facts_contradiction(const vector< vector<int> >& entrada, vector<pair<int, int> > facts)
{
    // Chacar se existe clausulas inteiras com zero (são todas negação dos fatos)
    for(unsigned i=0;i<entrada.size();i++)
    {
        int cont = 0;
        for(unsigned j=0;j<entrada[i].size();j++)
        {
            for(unsigned k=0;k<facts.size();k++)
            {
                if(entrada[i][j] == (entrada[facts[k].first][facts[k].second]) * (-1))
                {
                    cont++;
                }
            }

        }

        if((unsigned)cont == entrada[i].size() && cont > 1)
        {
            result(false);
            return true;
        }
    }

    return false;
}

int main(int argc, char* argv[])
{
    if(argc != 2)
    {
        cout << " > ERRO - comando incorreto.\n";
        return 0;
    }

    system("clear");
    cout << endl;
    cout << " [arquivo] " << argv[1] << endl;
    cout << " [algorit] hornSAT";

    vector< vector<int> > entrada     = openfile(argv[1]);
    vector< vector<int> > entrada_bkp = openfile(argv[1]);

    print_entrada(entrada);
    auto facts = simplifica(entrada);

    // adicionar a estrutura
    for(auto& item : facts)
    {
        int f = entrada_bkp[item.first][item.second];
        vector<int> temp;
        temp.push_back(f);
        entrada_bkp.push_back(temp);
    }

    bool contra = check_facts_contradiction(entrada_bkp, facts);
    if(contra) { return 0; }

    bool res = check_valid(entrada);
    if(res) { show_valoration(entrada_bkp); }

    return 0;
}
