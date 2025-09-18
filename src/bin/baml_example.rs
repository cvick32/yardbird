use anyhow::Result;
use baml_rust::models::{AnalysisType, VerificationContext, VerificationRequest};
use std::env;
use yardbird::baml_client::BamlClient;

#[tokio::main]
async fn main() -> Result<()> {
    // Check if BAML server is running
    let baml_url = env::var("BAML_URL").unwrap_or_else(|_| "http://localhost:2024".to_string());
    println!("Connecting to BAML server at: {}", baml_url);

    let client = BamlClient::new(Some(baml_url));
    println!("Connected to BAML server");
    // Create a sample verification context based on array_copy.vmt
    let context = VerificationContext {
        variables: vec![
            "i".to_string(), 
            "n".to_string(), 
            "a".to_string(), 
            "b".to_string(),
            "Z".to_string()
        ],
        init_conditions: "(= i 0)".to_string(),
        trans_conditions: "(and (= (store b i (select a i)) b_next) (< i n) (= (+ i 1) i_next) (= a a_next) (= n n_next) (= Z Z_next))".to_string(),
        property: "(=> (and (>= i n) (> Z 0) (< Z n)) (= (select a Z) (select b Z)))".to_string(),
        array_operations: vec!["select".to_string(), "store".to_string()],
        loop_bounds: vec!["(< i n)".to_string()],
        hints: vec!["Array copy loop".to_string()],
    };
    println!("Created Context");

    // Example 1: Propose Invariant
    println!("\n=== Example 1: Propose Invariant ===");
    let request1 = VerificationRequest {
        analysis_type: AnalysisType::ProposeInvariant,
        context: Box::new(context.clone()),
        failed_invariants: vec![],
        counterexample: None,
        current_strategy: Some("Abstract".to_string()),
    };

    match client.propose_invariant(request1).await {
        Ok(suggestions) => {
            println!("✅ Proposed Invariant: {}", suggestions.candidate_formula);
        }
        Err(e) => {
            eprintln!("❌ Failed to get invariant suggestions: {}", e);
        }
    }

    // Example 2: Analyze Counterexample
    println!("\n=== Example 2: Analyze Counterexample ===");
    let request2 = VerificationRequest {
        analysis_type: AnalysisType::AnalyzeCounterexample,
        context: Box::new(context.clone()),
        failed_invariants: vec!["(and (>= i 0) (<= i n))".to_string(), "(= a b)".to_string()],
        counterexample: Some("Model: i=5, n=3, a=[1,2,3], b=[1,2,0], Z=2".to_string()),
        current_strategy: Some("Abstract".to_string()),
    };

    match client.analyze_counterexample(request2).await {
        Ok(suggestions) => {
            println!(
                "✅ Counterexample Analysis: {}",
                suggestions.candidate_formula
            );
        }
        Err(e) => {
            eprintln!("❌ Failed to analyze counterexample: {}", e);
        }
    }

    // Example 3: Suggest Lemmas
    println!("\n=== Example 3: Suggest Lemmas ===");
    let request3 = VerificationRequest {
        analysis_type: AnalysisType::SuggestLemmas,
        context: Box::new(context),
        failed_invariants: vec![],
        counterexample: None,
        current_strategy: Some("Interpolation".to_string()),
    };

    match client.suggest_lemmas(request3).await {
        Ok(suggestions) => {
            println!("✅ Suggested Lemmas: {}", suggestions.candidate_formula);
        }
        Err(e) => {
            eprintln!("❌ Failed to get lemma suggestions: {}", e);
        }
    }

    Ok(())
}
