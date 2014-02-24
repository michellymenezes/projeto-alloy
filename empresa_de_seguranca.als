module empresaDeSeguranca

sig bairro{
	casas: set casa
}

sig autoBranco extends bairro{}

sig centro extends bairro{}

// Fato sobre bairro
fact nomeBairro {
	bairro = autoBranco + centro
}

sig casa{}

abstract sig servico{}

sig cercaEletrica extends servico{}

sig rondaNoturna extends servico{
	r: one cercaEletrica
}

sig monitoramentoCameras extends servico{
	r: one cercaEletrica
}
