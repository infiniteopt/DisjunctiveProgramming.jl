using Coverage

function run_coverage_analysis()
    # Get the directory of this file
    pkg_dir = dirname(@__DIR__)
    
    # Change to package directory
    cd(pkg_dir) do
        # Clean up previous coverage files
        clean_folder(".")
        
        # Run tests with coverage
        println("Running tests with coverage...")
        run(`$(Base.julia_cmd()) --code-coverage=user test/runtests.jl`)
        
        # Process coverage data
        println("\nAnalyzing coverage...")
        coverage = process_folder("src")  # Only process src/ directory
        
        # Generate and display coverage report
        covered, total = get_summary(coverage)
        coverage_pct = round((covered / total) * 100, digits=2)
        
        println("\n=== Coverage Summary ===")
        println("Covered lines: $covered / $total")
        println("Coverage: $coverage_pct%")
        
        # Generate detailed report
        # println("\n=== File-by-File Coverage ===")
        # for file in coverage
        #     file_cov, file_total = get_summary([file])
        #     if file_total > 0
        #         pct = round((file_cov / file_total) * 100, digits=1)
        #         # println("$(rpad(basename(file.filename), 30)) $(lpad(string(pct), 5))%")
        #     end
        # end
        
        return coverage
    end
end

# Run the analysis
run_coverage_analysis()