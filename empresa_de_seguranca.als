module bairro

sig bairro{
	casas: set casa
}

sig auto_branco extends bairro{}

sig centro extends bairro{}

sig casa{}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{}

sig monitoramentoCameras extends servico{}
